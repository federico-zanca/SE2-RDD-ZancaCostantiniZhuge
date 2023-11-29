abstract sig User {}

sig Student extends User {
    teams: set Team
}

sig Educator extends User {
    tournaments: set Tournament,
    battles: set Battle
}

sig Team {
    students: set Student,
    battle: Battle,
    score: Int
}

sig Battle {
    minStudents: Int,
    maxStudents: Int,
    registrationDeadline: Time,
    submissionDeadline: Time,
    tournament: Tournament,
    teams: set Team
}

sig Tournament {
    creator: Educator,
    battles: set Battle,
    students: set Student
}

sig Time {}

fact {
    all b: Battle | b.minStudents <= #b.teams.students and #b.teams.students <= b.maxStudents
    all t: Tournament | all b: t.battles | b.tournament = t
    all s: Student | all t: s.teams | some b: t.battle | b in s.teams.battle.tournament.battles
}