open util/boolean

//-----------------DATATYPE DEFINITION----------------//
one sig Email{}
one sig Integer{}
one sig Strings{}
abstract sig Date {
	day: one Integer,
	month: one Integer,
	year: one Integer
}
abstract sig User {}
sig DateBirth extends Date {}

sig PersonalData {
firstName: one Strings, 
lastName: one Strings,
sex: one Strings,
emailAddress: one Email,
dateOfBirth: one DateBirth,
birthPlace: one Strings,
actualAddress: one Strings,
city: one Strings,
phoneNumber: one Strings,
drivingLicenceNumber: one Strings,
taxIDCode: one Strings
}

sig PaymentCardData {
paymentCardNumber: one Strings,
paymentCardSecurityCode: one Strings
}


sig Password {}


//---------------SIGNATURES-----------------------------//
sig Visitor extends User{}

sig RegisteredUser extends User {
personalData: one PersonalData,
paymentData: one PaymentCardData,
newPassword: one Password,
loggedIn: one Bool,
disabled: one Bool
}

one sig PowerEnjoyUserDB {
	registeredUsers: set RegisteredUser,
	loggedInUsers: set RegisteredUser
}

sig Registration {
registrates: one RegisteredUser,
regId: one Integer,
dataChecker: one DataCheckingSystem
}

one sig DataCheckingSystem {
	correctData: one Bool
}

//---------------FACTS----------------------------------//
fact dateNonempty {
	all d: Date | (#d.year=1) and (#d.month=1) and (#d.day=1)
}

fact dataCheckNonempty {
	all d: DataCheckingSystem | (#d.correctData=1)
}
fact userNonempty {
	all u: User | (#u.loggedIn=1) and (#u.personalData=1) and (#u.newPassword=1) and (#u.paymentData=1)
}
fact registrationNonempty {
	all r: Registration | (#r.registrates=1)  and (#r.dataChecker=1)
}
fact personalDataNonempty {
	all p: PersonalData | (#p.firstName=1) and (#p.lastName=1) and (#p.sex=1) and (#p.emailAddress=1) and 
										(#p.dateOfBirth=1) and (#p.birthPlace=1) and (#p.actualAddress=1) and (#p.city=1) and
										(#p.phoneNumber=1) and (#p.drivingLicenceNumber=1) and (#p.taxIDCode=1)
}
fact paymentNonempty {
	all p: PaymentCardData | (#p.paymentCardNumber=1) and (#p.paymentCardSecurityCode=1)
}

fact noDuplicateUser {
	no disj u1, u2: RegisteredUser | u1.personalData.emailAddress = u2.personalData.emailAddress
}

fact noDuplicateRegistration {
	no disj r1, r2: Registration | r1.regId=r2.regId
}

fact registration {
	all u: RegisteredUser | one r: Registration | r.registrates = u
}

fact accountDisabled {
	all u: RegisteredUser | u.disabled= True => u not in PowerEnjoyUserDB.registeredUsers
}


fact userMemorized {
	all u: RegisteredUser | u in PowerEnjoyUserDB.registeredUsers
}

fact registrationDoneIfDataAreCorrect {
	all r: Registration| r.dataChecker.correctData = True
}

fact login {
	all u: RegisteredUser | u.loggedIn=True
}

fact logoutIssue {
	all u: RegisteredUser | u not in PowerEnjoyUserDB.loggedInUsers => u.loggedIn= False
}

//--------------PREDICATES---------------------------//
pred show {}

pred addNewUser(u: RegisteredUser, pdb1, pdb2: PowerEnjoyUserDB) {
	u not in pdb1.registeredUsers implies pdb2.registeredUsers = pdb1.registeredUsers + u and u.disabled= False
}

pred deleteUser (u: RegisteredUser, pdb1, pdb2: PowerEnjoyUserDB) {
	u in pdb1.registeredUsers and u.disabled = True implies pdb2.registeredUsers= pdb1.registeredUsers- u
}

pred login (u: RegisteredUser, p1, p2: PowerEnjoyUserDB) {
	u not in p1.loggedInUsers and u.loggedIn= True implies p2.loggedInUsers = p1.loggedInUsers + u 
}

pred logout (u: RegisteredUser, p1, p2: PowerEnjoyUserDB) {
	u in p1.loggedInUsers and u.loggedIn= False implies p2.loggedInUsers = p1.loggedInUsers - u
}

run show for 4
run addNewUser for 2
run deleteUser for 2
run login for 2
run logout for 2

//-------------ASSERTIONS---------------------------//


assert addNewUser {
	all u: RegisteredUser, pdb1, pdb2: PowerEnjoyUserDB | (u not in pdb1.registeredUsers) and addNewUser[u, pdb1, pdb2] implies (u in pdb2.registeredUsers) and u.disabled=False
}

assert deleteUser {
	all u: RegisteredUser, pdb1, pdb2: PowerEnjoyUserDB | (u in pdb1.registeredUsers) and u.disabled= True and deleteUser[u, pdb1, pdb2] implies (u not in pdb2.registeredUsers)
}

assert login {
	all u: RegisteredUser, pdb1, pdb2: PowerEnjoyUserDB | (u not in pdb1.loggedInUsers) and u.loggedIn= True and login[u, pdb1, pdb2] implies (u in pdb2.loggedInUsers)
}

assert logout {
	all u: RegisteredUser, pdb1, pdb2: PowerEnjoyUserDB | (u in pdb1.loggedInUsers) and u.loggedIn= False and logout[u, pdb1, pdb2] implies (u not in pdb2.loggedInUsers)
}

check addNewUser
check deleteUser
check login 
check logout
