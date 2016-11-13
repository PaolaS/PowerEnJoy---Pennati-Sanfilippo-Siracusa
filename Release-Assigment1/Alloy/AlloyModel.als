open util/boolean

abstract sig BatteryLevel {}
	one sig LowBattery extends BatteryLevel {}			// 0%	< BatteryLevel		< 20%
	one sig MediumBattery extends BatteryLevel {}		// 20%	<= BatteryLevel	< 50%
	one sig HighBattery extends BatteryLevel {}			// 50%	<= BatteryLevel	< 100

abstract sig DistanceCarToPowerGridStation {}
	one sig Close extends DistanceCarToPowerGridStation {}  // Car 50m near a Power grid station
	one sig Medium extends DistanceCarToPowerGridStation {}  // Car from 50m to 3Km far away a Power grid station
	one sig Far extends DistanceCarToPowerGridStation {}  // Car 3Km far away a Power grid station

abstract sig DistanceUserCarForUnlocking {}
	one sig InUnlockingRange extends DistanceUserCarForUnlocking {}  // User within 100m from the reserved car
	one sig OutUnlockingRange extends DistanceUserCarForUnlocking {}  // User not within 100m the reserved car

abstract sig DistaceCarToResearchPosition {}
	one sig InResearchRange extends DistaceCarToResearchPosition {}  // Car within 500m from the research position
	one sig OutResearchRange extends DistaceCarToResearchPosition {}  // Car not within 500m from the research position

abstract sig SessionStatus {}
	one sig Reservation extends SessionStatus {}
	one sig ReservationClosed extends SessionStatus {}
	one sig UnlockingRange extends SessionStatus {}
	one sig Driving extends SessionStatus {}
	one sig CostAssessment extends SessionStatus {}

sig Person{ }
sig Visitor extends Person{ }

sig User extends Visitor {
	owing: one Bool, // If the user owes the system or not
	loggedIn: one Bool,
	pledgeOk: one Bool,
	session: lone ActiveSession
} {
	this not in session.recordedPassengers
	
	// A: Only users that have paid all the previous sessions can reserve a car
	session != none implies owing = False
	
	// A: Only logged in users can reserve a car
	session != none implies loggedIn = True

	// A: An user cannot be a passenger of itself
	session != none && this not in session.recordedPassengers
}

sig PowerGridStation { }

sig Car {
	pluggedAt: lone PowerGridStation,
	batteryLevel: one BatteryLevel,
	locked: one Bool,
	distanceNextPGS: one DistanceCarToPowerGridStation
} {
	#pluggedAt != 0 implies distanceNextPGS = Close
}

sig PossiblePGS {
	pgs: one PowerGridStation,
	distanceToDestination: one Int,
	pluggedCars: one Int
} {
	pluggedCars = pluggedCars[pgs]
	distanceToDestination >= 0
}


//Note: the model does not comprehend the distance of the powerGridStation to the destination
// There would be picked out the nearest one
sig MoneySavingOption {
	ppgs: set PossiblePGS, // possible ones
	cpgs: lone PossiblePGS // Chosen one
} {
	#ppgs !=0 implies #cpgs != 0
	let p = PossiblePGS | p in ppgs iff p.pluggedCars < 2
	all k: PossiblePGS | k in ppgs && cpgs.distanceToDestination <= k.distanceToDestination
}

sig FinalCost {
	fee: one Bool,				// 1€ fee for having got to the car too late
	discount1: one Bool, 	// 10% discount with at least 2 passenger
	discount2: one Bool,		// 20% discount ending the ride with Battery >= 50%
	discount3: one Bool,		// 20% discount plugging the car to a power grid station ending the ride
	charge1: one Bool,		// 30% charge ending the ride with Battery < 20% or 3Km far away any power grid station
}

// Note: the pay session prevents the user reserving other cars since the user can have just one session active
sig ActiveSession {
	status: one SessionStatus,
	car: one Car,
	moneySavingOption: lone MoneySavingOption,
	duc: one DistanceUserCarForUnlocking,
	dcp: one DistanceCarToPowerGridStation, // Distance to the next one
	overPluggingTime: one Bool,
	overReservationTime: one Bool,
	finalCost: lone FinalCost,
	recordedPassengers: set User,
	onBoardPassengers: set User,
	driverOnBoard: one Bool,
} {
	
	//A: At most 4 passengers
	#recordedPassengers < 4

	// User far away from the car => cannot be on board
	duc = OutUnlockingRange implies driverOnBoard = False
	// User on board => user close to the car
	driverOnBoard = True implies duc = InUnlockingRange

	#recordedPassengers = 0 implies #onBoardPassengers = 0
	#onBoardPassengers != 0 implies onBoardPassengers = recordedPassengers
	status = Driving iff onBoardPassengers = recordedPassengers

	status = Reservation iff ( 
						car.batteryLevel != LowBattery &&
						#moneySavingOption = 0 &&
						car.locked = True && 
						duc = OutUnlockingRange &&
						//dcp = NOT RELEVANT &&
						overPluggingTime = False &&
						overReservationTime = False &&
						#finalCost = 0 &&
						#recordedPassengers = 0 &&
						#onBoardPassengers = 0 &&
						driverOnBoard = False
					)

	status = ReservationClosed iff ( 
						car.batteryLevel != LowBattery &&
						#moneySavingOption = 0 &&
						car.locked = True && 
						duc = OutUnlockingRange &&
						//dcp = NOT RELEVANT &&
						overPluggingTime = False &&
						overReservationTime = True &&
						#finalCost != 0 &&
						#recordedPassengers = 0 &&
						#onBoardPassengers = 0 &&
						driverOnBoard = False
					)

	status = UnlockingRange iff ( 
						car.batteryLevel != LowBattery &&
						#moneySavingOption = 0 &&
						car.locked = True && 
						duc = InUnlockingRange &&
						//dcp = NOT RELEVANT &&
						overPluggingTime = False &&
						overReservationTime = False &&
						#finalCost = 0 &&
						#recordedPassengers = 0 &&
						#onBoardPassengers = 0 &&
						driverOnBoard = False
					)

	status = Driving iff ( 
						//car.batteryLevel = NOT RELEVANT &&
						//#moneySavingOption = NOT RELEVANT &&
						car.locked = False && 
						duc = InUnlockingRange &&
						//dcp = NOT RELEVANT &&
						overPluggingTime = False &&
						overReservationTime = False &&
						#finalCost = 0 &&
						//#recordedPassengers = NOT RELEVANT &&
						//#onBoardPassengers = NOT RELEVANT &&
						driverOnBoard = True
					)

	status = CostAssessment iff ( 
						//car.batteryLevel = NOT RELEVANT &&
						#moneySavingOption = 0 &&
						car.locked = True && 
						//duc = NOT RELEVANT &&
						//dcp = NOT RELEVANT &&
						overPluggingTime = True &&
						overReservationTime = False &&
						#finalCost != 0 &&
						//#recordedPassengers = NOT RELEVANT &&
						#onBoardPassengers = 0 &&
						driverOnBoard = False
					)

	// A: A car cannot be plugged when in movement
	status = Driving implies ( no pgs: PowerGridStation | car.pluggedAt = pgs )

		finalCost.fee = True iff status = ReservationClosed
		finalCost.discount1 = True iff 	#recordedPassengers >= 2
		finalCost.discount2 = True iff car.batteryLevel = HighBattery
		finalCost.discount3 = True iff ( #car.pluggedAt != 0 )
		finalCost.charge1 = True iff ( car.batteryLevel = LowBattery or car.distanceNextPGS = Far )


}

fun pluggedCars[pgs: PowerGridStation] : one Int {
	#pluggedAt :> pgs
}


// A: Any plug station has exactly 4 electric outlets (plugs) available
fact plugsLimit {
	all pgs: PowerGridStation | pluggedCars[pgs] <= 4
}

// A: Any session needs an user (person) associated
fact noSessionsWithNoUser {
	all s: ActiveSession | one u: User | u.session = s
}

// A: Any Money saving option needs a session associated
fact noMSOWithNoSession {
	all mso: MoneySavingOption | one s: ActiveSession | s.moneySavingOption = mso
}

// A: Any PossiblePGS needs a MoneySavingOption associated
fact noPossiblePGSWithNoMoneySavingOption {
	all p: PossiblePGS | one mso: MoneySavingOption | p in mso.ppgs
}

// It comes up from the model sempification of the distance PGS-Car
fact PossiblePGLessEqPGS1 {
	no mso: MoneySavingOption | #mso.ppgs > #PowerGridStation
}

// It comes up from the model sempification of the distance PGS-Car
fact PossiblePGLessEqPGS2 {
	no disjoint ppgs1, ppgs2: PossiblePGS, mso: MoneySavingOption | ( (ppgs1 in mso.ppgs) and (ppgs2 in mso.ppgs) ) implies ( ppgs1.pgs = ppgs2.pgs )
}

// A: No people on board in different places at the same time
fact noOnBoardDifferentPlacesSameTime {
	all u: User | ( ( u.session.driverOnBoard = True ) implies u not in ActiveSession.onBoardPassengers )
	no disjoint s1, s2: ActiveSession | s1.onBoardPassengers & s2.onBoardPassengers != none
}

// A: one car only for each session
fact oneCarForEachSession {
	no disjoint s1, s2: ActiveSession | #s1.car != 0 && s1.car = s2.car 
}

// Any car without a session should be locked
fact carWithNoSessionLocked {
	no c: Car | #ActiveSession.car = 0 && c.locked = False
}

//A: The final cost, if exists, should be linked at a session
fact noFinalCostWithoutSession {
	no f: FinalCost | f not in ActiveSession.finalCost
}

//////////////////////////////////////////////////////////////////////

pred reserveACar[u: User] { // G|u3
	u.owing = False and u.loggedIn = True and u.pledgeOk = True and
	some c: Car | ActiveSession.car != c
}
//run reserveACar for 5

assert notReservableIfBatteryLessThan20 {
	all s: ActiveSession | s.status = Reservation and  s.car.batteryLevel != LowBattery
}
//check notReservableIfBatteryLessThan20

assert closeTheReservationIfLate { // G|u04
	all s: ActiveSession | s.overReservationTime = True implies s.finalCost.fee = True
}
//check closeTheReservationIfLate

pred unlockTheReservedCar[u: User] { // G|u05
	u.session.overReservationTime = False and u.session.duc = InUnlockingRange iff u.session.status = UnlockingRange
}
//run unlockTheReservedCar for 5

assert discount10p { // G|u06
	all u: User | u.session.status = CostAssessment && #recordedPassengers >= 2 implies u.session.finalCost.discount1 = True
}
//check discount10p

assert discount20p { // G|u07
	all u: User | u.session.status = CostAssessment && u.session.car.batteryLevel = HighBattery implies u.session.finalCost.discount2 = True
}
//check discount20p

assert discount30p { // G|u08
	all u: User | u.session.status = CostAssessment && #u.session.car.pluggedAt > 0 implies u.session.finalCost.discount3 = True
}
//check discount30p

assert charge30p { // G|u09
	all u: User | u.session.status = CostAssessment && u.session.car.batteryLevel = LowBattery or u.session.car.distanceNextPGS = Far implies u.session.finalCost.charge1 = True
}
//check charge30p

assert activeMSO { // G|u11
	all s: ActiveSession | #s.moneySavingOption > 0 && #s.moneySavingOption.ppgs > 0 implies #s.moneySavingOption.cpgs.pgs > 0
}
//check activeMSO

pred show() {}

run show

