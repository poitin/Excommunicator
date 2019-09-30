DEFINITIONS

AuthenticateUser{} = new user.(new pwd.(new role. (checkUser().login(user,pwd).checkID<user,pwd>.userStatus(role).
if (role = Dispensator) then validUser<user>.0 else invalidPwd<>.0 fi . 0)))

CheckUserandCard{} = new user.(new cardUser.(validUser(user).validCard(cardUser).
if (user = cardUser) then userAuthenticated<>.0 else wrongCard<>.0 fi. 0))

ReadSmartCard{} = new cardNum.(checkCard(). cardInserted(cardNum). queryCardDb<cardNum>.0)

GetCardUser{} = new cardNum. (new user. (queryCardDb(cardNum).query<cardNum>.cardOwner(user).
if (user <> null) then validCard<user>.0 else badCard<>.0 fi .0))

ValidateUser{} = dispensationModuleStarted().(checkUser<>.0|checkCard<>.0).0

AccessDispensationModule{} = dispensationModuleStarted<>.0

IdentifyPatientandLoadData{} = userAuthenticated().0

GUI{} = login[1.0,3.0] <David,knock>.0

AuthenticationService{} = new user.(checkID (user,pwd).(userStatus[0.5,1.0]<Dispensator>.0 + userStatus[0.5,1.0]<nonDispensator>.0).0)

SmartCardReader{} = cardInserted[1.0,1.5]<C1>.0

SmartCardDatabase{} = new num.(query(num). if (num = C1) then cardOwner[0.0,0.25]<David>.0 else cardOwner[0.0,0.25]<null>.0 fi .0)

ENDD


SYSTEM

AccessDispensationModule{} | ValidateUser{} | AuthenticateUser{} | ReadSmartCard{} | GetCardUser{} | CheckUserandCard{} |
IdentifyPatientandLoadData{} | SmartCardReader{} | SmartCardDatabase{} | AuthenticationService {} | GUI{}

ENDS


PROPERTIES

userAuthenticated() > validUser(*) and userAuthenticated() > validCard(*)
userAuthenticated() before [dispensationModuleStarted()+5.0, dispensationModuleStarted() + 6.0]


ENDP
