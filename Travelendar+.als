sig Stringa{}

sig User{
	name: one Stringa,
	surname: one Stringa,
	credentials: one Credentials,
	attend: set Meeting
}

sig Credentials{
	username: one Stringa,
	password: one Stringa
}

sig Meeting{
	state: one MeetingState,
	stage: some Stage
}

sig Stage{
	state: one MeetingState,
	beginDate: one Int,
	endDate: one Int
}{beginDate >= 0 and endDate > beginDate}

abstract sig MeetingState{}
sig IN_PROGRESS extends MeetingState{}
sig SCHEDULED extends MeetingState{}
sig COMPLETED extends MeetingState{}

sig System{
	currentTime: one Int
}{currentTime>=0}

//un solo sistema
fact f0{
	#System = 1
}

//non esistono due persone con lo stesso username
fact f1{
	no disj u1, u2: User | u1.credentials.username = u2.credentials.username
}

//non esistono credenziali senza il corrispettivo proprietario
fact f2{
	all c: Credentials | one u : User | u.credentials = c
}

//se un meeting è completato allora tutti i suoi stages sono completati
fact f3{
	all m: Meeting | all s: Stage | s in m.stage and 
		m.state in COMPLETED implies s.state in COMPLETED
}

//se un meeting è solo programmato, allora tutti i suoi stage sono solo programmati
fact f4{
	all m: Meeting | all s: Stage | s in m.stage and 
		m.state in SCHEDULED implies s.state in SCHEDULED
}

//se un meeting è in corso allora esiste uno e un solo stage in corso relativo al meeting
fact f5{
	all m: Meeting | m.state in IN_PROGRESS implies 
		(one s: Stage | s in m.stage and s.state in IN_PROGRESS)
}

//un utente può avere al massimo un solo meeting in corso
fact f6{
	all u: User | lone m:Meeting | m in u.attend and m.state in IN_PROGRESS
}

//non esistono meeting senza il corrispettivo proprietario
fact f7{
	all m: Meeting | some u : User | m in u.attend
}

//non esistono stage senza il corrispettivo meeting
fact f8{
	all s: Stage | one m : Meeting | s in m.stage
}

//tutti gli stage antecedenti alla data corrente sono completati
//fact f9{
//	all s: Stage | all sys: System | s.endDate <= sys.currentTime
//		implies (s.state in COMPLETED)
//}

//tutti gli stage antecedenti alla data corrente sono completati
fact f9{
	all s: Stage | s.state in COMPLETED
		implies (all sys: System | s.endDate <= sys.currentTime)
}

//tutti gli stage programmati dopo la data corrente sono nello stato di scheduling
fact f10{
	all s: Stage | s.state in SCHEDULED
		implies (all sys: System | s.beginDate >= sys.currentTime)
}

//tutti gli stage in corso hanno sys.currentTime compreso tra inizio e fine
fact f11{
	all s: Stage | s.state in IN_PROGRESS
		implies (all sys: System | s.beginDate < sys.currentTime
			and sys.currentTime < s.endDate)
}

//gli stages nei meeting sono ben formati (contiguità e coerenza)
fact f12{
	all m: Meeting | #m.stage > 1 implies
			((one s: Stage| s in m.stage and no e:Stage|
				s.beginDate = e.endDate) and
			(one s: Stage| s in m.stage and no e:Stage|
				e.beginDate = s.endDate))
}

//non ci sono più stages che iniziano allo stesso tempo nello stesso meeting
fact f13{
	no disj s1,s2: Stage | one m: Meeting |
		s1 in m.stage and s2 in m.stage and s1.beginDate = s2.beginDate
}

//non ci sono più stages che finiscono allo stesso tempo nello stesso meeting
fact f14{
	no disj s1,s2: Stage | one m: Meeting |
		s1 in m.stage and s2 in m.stage and s1.endDate = s2.endDate
}

pred show{
	one m: Meeting | #m.stage = 4
}
run show for 2 but 4 Stage
