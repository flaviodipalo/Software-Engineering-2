sig Stringa{}

sig User{
	name: one Stringa,
	surname: one Stringa,
	username: one Stringa,
	password: one Stringa,
	attend: set Activity
}

abstract sig Activity{
	state: one ActivityState,
	route: lone Route,
	schedulingDate: one Int,
	endActivityDate: one Int,
	alert: set Warning
}{
	schedulingDate >= 0 and
	endActivityDate > schedulingDate
}

sig Meeting extends Activity{}

sig FlexibleActivity extends Activity{
	schedulingIntervalBegin: one Int,
	schedulingIntervalEnd: one Int
}{
	schedulingIntervalBegin >= 0 and
	schedulingIntervalEnd > schedulingIntervalBegin
}

sig Route{
	stage: some SubRoute
}

sig SubRoute{
	state: one ActivityState,
	beginDate: one Int,
	endDate: one Int,
	alert: lone Warning
}{
	beginDate >= 0 and 
	endDate > beginDate
}

abstract sig ActivityState{}
sig IN_PROGRESS extends ActivityState{}
sig SCHEDULED extends ActivityState{}
sig COMPLETED extends ActivityState{}

abstract sig Warning{}
sig UNREACHABLE extends Warning{}
sig RAIN extends Warning{}
sig STRIKE extends Warning{}

//Used for time clock
sig System{
	currentTime: one Int
}{
	currentTime>=0
}

//There is only one system with its current Time
fact onlyOneSystem{
	#System = 1
}

//There is not two users with the same username
fact noTwoUsersWithSameUsername{
	no disj u1, u2: User | u1.username = u2.username
}

//An Activity is completed if and only if it's already finished 
fact completedActivity{
	all a: Activity | a.state in COMPLETED
		iff
	(all sys: System | sys.currentTime >= a.endActivityDate)
}

//An Activity is scheduled if and only if has not yet begun 
// and neither the route has begun
fact scheduledActivity{
	all a: Activity, sys: System | a.state in SCHEDULED
		iff
	 (sys.currentTime =< a.schedulingDate and
	  (all s: SubRoute | s in a.route.stage implies s.state in SCHEDULED))
}

//Each activity has its (unique) creator
fact allActivityhasACreator{
	all a: Activity | one u : User | a in u.attend
}

//There are no routes without the corresponding activity
fact allRouteshasAMotherActivity{
	all r: Route | one a : Activity | r in a.route
}

//There are no subroutes without the corresponding route
fact allSubRouteshasAMotherRoute{
	all s: SubRoute | one r : Route | s in r.stage
}

//All subroutes scheduled prior to the current date are completed
fact completedSubRoute{
	all s: SubRoute | s.state in COMPLETED
		iff
	(all sys: System | s.endDate <= sys.currentTime)
}

//All subroutes scheduled after to the current date are scheduled
fact scheduledSubRoute{
	all s: SubRoute | s.state in SCHEDULED
		iff
	(all sys: System | s.beginDate >= sys.currentTime)
}

//all subroutes in progress have sys.currentTime between 
//begin-time and end-time
fact inProgressSubRoute{
	all s: SubRoute | s.state in IN_PROGRESS
		iff
			(all sys: System | s.beginDate < sys.currentTime
				and sys.currentTime < s.endDate)
}

//there can be no two activities at the same time
//e.g. Luca has two meeting, one from 2:00 to 5:00 and 
// one from 3:00 to 6:00. This is impossible because at 4:00 Luca 
//should attend two different meetings
fact noTwistedActivity{
	no disj a1, a2: Activity | one u: User |
		a1 in u.attend and a2 in u.attend and
			(some t: Int | 
				t >= a1.schedulingDate and
				t >= a2.schedulingDate and 
				t < a1.endActivityDate and
				t < a2.endActivityDate
			)
}

//The example also applies to subroutes: 
//If I'm traveling for meeting 2 then
//I can not attend the meeting 1 at the same time
fact noTwistedActivityOneWithARoute{
	no disj a1, a2: Activity | one u: User |
		#a1.route = 1 and #a2.route = 0 and
		a1 in u.attend and a2 in u.attend and
			(some t: Int | 
				t >= a2.schedulingDate and 
				t < a1.endActivityDate and
				t < a2.endActivityDate and
				(some s1: SubRoute | s1 in a1.route.stage and
					t >= s1.beginDate)
			)
}

//The example also applies to two subroutes: 
//If I'm traveling for meeting 1 then
//I can not traveling for meeting 2 at the same time
fact noTwistedActivityTwoWithARoute{
	no disj a1, a2: Activity | one u: User |
		#a1.route = 1 and #a2.route = 1 and
		a1 in u.attend and a2 in u.attend and
			(some t: Int | 
				t < a1.endActivityDate and
				t < a2.endActivityDate and
				(some s1: SubRoute | s1 in a1.route.stage and
					t >= s1.beginDate) and
				(some s2: SubRoute | s2 in a2.route.stage and
					t >= s2.beginDate)
			)
}

//there can be no two subroutes related of the same route 
//scheduled at the same time
fact noTwistedSubRoutes{
	no disj s1, s2: SubRoute | one r: Route |
		s1 in r.stage and s2 in r.stage and
			(some t: Int | t >= s1.beginDate and
				t >= s2.beginDate and 
				t < s1.endDate and
				t < s2.endDate)
}

//there can no be a subroute scheduled after the end of activity
fact noLateOrUselessSubRoutes{
	no s: SubRoute | one a: Activity |
		s in a.route.stage and
		s.endDate >= a.endActivityDate
}

//all flexible activities must comply with their construction constraint
fact allFlexibleActivityAreScheduledInTheGivenInterval{
	all f: FlexibleActivity |
		f.schedulingIntervalEnd >= f.endActivityDate and
		f.schedulingIntervalBegin =< f.schedulingDate and
		(all s: SubRoute | s in f.route.stage implies
			f.schedulingIntervalBegin =< s.beginDate)
}

//WARNING CONSTRAINS

//a warning always belongs to one activity
fact oneActivityForEachWarning{
	all w: Warning | one a:Activity| w in a.alert
}

//a warning always belongs to one or zero subroute
fact oneSubRouteForEachWarning{
	all w: Warning | lone s:SubRoute | w in s.alert
}

//if an activity contains a warning and a route then 
//there is a subroute that caused that warning. 
//This subroute belongs to the activity's route
fact thereIsAlwaysACauseOfTheWarning{
	all a: Activity | #a.route = 1 implies a.alert = a.route.stage.alert
}

//an activity without a route can have unreachable warning,
//e.g. Luca, in Italy, wants to arrive at New York in 5 minutes
fact activityWithoutRouteCanHaveOnlyUnreachableWarning{
	all a: Activity | #a.route = 0 implies
		(all w: Warning | w in a.alert implies w in UNREACHABLE)
}

//a subroute is called unreachable if it makes the user late for
// the appointment.
fact definitionOfUnreachableSubRoute{
	all s: SubRoute |
		(some u: UNREACHABLE | u in s.alert)
			iff
		(s.endDate > s.~stage.~route.schedulingDate)
}

//the system can not scheduled unreachable flexible activity when 
//it can fine scheduled the same flexible activity reachable.
fact noUselessUnreachableWarningForFlexibleActivities{
	all f: FlexibleActivity |
		(some u: UNREACHABLE | u in f.alert)
			implies
		((some a: Activity | f.endActivityDate = a.schedulingDate 
			and f.~attend = a.~attend)
				or
		(some s: SubRoute | f.endActivityDate = s.beginDate
			and f.~attend = s.~stage.~route.~attend))
}

//if an activity with a route is completed then all its subroutines,
//that belongs to the activity's route, are completed
assert completedSubRoutesOnCompletedActivity{
	all a: Activity | a.state in COMPLETED and #a.route = 1 
		implies
	(all s: SubRoute | s in a.route.stage implies a.state in COMPLETED) 
}
//check completedSubRoutesOnCompletedActivity
//OK

//if an activity with a route is scheduled then all its subroutines,
//that belongs to the activity's route, are scheduled
assert scheduledSubRoutesOnScheduledActivity{
	all a: Activity | a.state in SCHEDULED and #a.route = 1 
		implies
	(all s: SubRoute | s in a.route.stage implies a.state in SCHEDULED) 
}
//check scheduledSubRoutesOnScheduledActivity
//OK

//if an activity with a route is in progress then there at most one subroute
// in progress
assert subRoutesConstrainsOnActivityInProgress{
	all a: Activity  | a.state in IN_PROGRESS and #a.route = 1
		implies
			(lone s: SubRoute | s in a.route.stage and s.state in IN_PROGRESS)
}
//check subRoutesConstrainsOnActivityInProgress
//OK

//A user can have at most one activity in progress
assert onlyOneActivityInProgressForEachUser{
	all u: User | lone a:Activity | 
		a in u.attend and a.state in IN_PROGRESS
}
//check onlyOneActivityInProgressForEachUser
//OK

//If an activity has no warning then all his subroutes has no warning
assert noWarningActivityImpliesNoWarningSubRoutes{
	all a: Activity | a.alert = none implies
		(all s: SubRoute | s in a.route.stage implies s.alert = none)
}
//check noWarningActivityImpliesNoWarningSubRoutes
//OK

pred twousers{
	#User = 2
	#Activity = 3
	#{x: Warning | x in UNREACHABLE} > 0
}

pred activitywithoutroute{
	#User = 1
	#{x: Activity | #x.route = 0} >= 1
	#Activity > 2
}

pred rainday{
	#User < 3
	#RAIN = 3
	#{x: Warning | x not in RAIN} = 0
	#{x: Meeting | #x.alert = 1} = 1
}

pred show{
	#User = 1
	#{x: FlexibleActivity | not x.alert = none} = 1
	#{x: Warning | x not in UNREACHABLE} = 1
	#{x: Activity | x.state in IN_PROGRESS} > 0
}
run show for 3 but exactly 4 SubRoute, exactly 2 Route
