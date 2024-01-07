enum UserStatus{NotSigned, Signed}

enum TournamentStatus{NotCreatedT, OpenT, InProgressT, ClosedT}

enum BattleStatus{NotCreatedB, OpenB, InProgressB, ClosedB}

enum TeamStatus{NotCreatedTeam, CreatedTeam}

enum ScoreStatus{NotCreatedS, CreatedS}

enum BadgeType{ParticipationBadge, TeamBadge, DoubleDigitScoreBadge}

abstract sig User{
    username: one Int,
    var uStatus: one UserStatus
}

sig Student extends User{
    var sBadges: set BadgeType
}

sig Educator extends User{}



sig Tournament{
    var participants: set Student,
    var leaderBoard: disj set Score,
    var administrators: set Educator,
    var tStatus: one TournamentStatus,
    var tBattles: disj set Battle,
    var tBadges: set BadgeType
}

sig Team{
    var members: set Student,
    var teamStatus: one TeamStatus,
    size: one Int,
    var score: one Int
}

sig Battle{
    var bStatus: one BattleStatus,
    var bTeams: disj set Team,
    minSize: one Int,
    maxSize: one Int
}

sig Score{
    var student: lone Student,
    var sStatus: one ScoreStatus,
    var value: one Int,
    var rank: one Int
}


// --------------------------- USER FACTS

// Signed Users remain signed

fact StateTransitionsU{
    always all u: User | isSigned[u] implies (always isSigned[u])
}

// Two users can't have the same username
fact DiffUsername{
    always all u1, u2: User | u1 != u2 implies u1.username != u2.username
}

// ------------------------- STUDENT FACTS

// If a user has acquires a badge, it will stay in its history
fact studentConsistency{
    always all s: Student, b: BadgeType | once b in s.sBadges implies always b in s.sBadges
}


// -------------------------- TOURNAMENT FACTS

// Consistency between states transition in Tournaments

fact StateTransitionsT{
    always all t: Tournament | isNotCreatedT[t] implies (isNotCreatedT[t] until isOpenT[t])
    always all t: Tournament | isOpenT[t] implies (isOpenT[t] until (isInProgressT[t] || isClosedT[t]))
    always all t: Tournament | isInProgressT[t] implies (isInProgressT[t] until isClosedT[t'])
    always all t: Tournament | isClosedT[t] implies always isClosedT[t]
}

// When changing status, Tournament maintains its participants/educators

fact ConsistencyStatesT{
    always all t: Tournament, s: Student | once s in t.participants implies always s in t.participants
    always all t: Tournament, e: Educator | once e in t.administrators implies always e in t.administrators
    always all t: Tournament, b: Battle | once b in t.tBattles implies always b in t.tBattles
    always all t: Tournament, b: BadgeType | once b in t.tBadges implies always b in t.tBadges
}

// A Tournament can be inProgress only if there are students in it

fact MeaningfulT{
    always all t: Tournament | isInProgressT[t] implies #t.participants > 0
}


// Students and Educators in a torunament must be signed

fact UsersSigned{
    always all t: Tournament, s: t.participants | s.uStatus = Signed
    always all t: Tournament, e: t.administrators | e.uStatus = Signed
}


// Every tournament must have an administrator associated

fact wasCreated{
    always all t: Tournament | t.tStatus != NotCreatedT implies #t.administrators > 0
    always all t: Tournament | t.tStatus = NotCreatedT implies (#t.administrators = 0 && #t.participants = 0 && #t.tBattles = 0 && #t.leaderBoard = 0 && #t.tBadges = 0)
}

// A Tournament can be closed if all his battles are closed

fact CanBeClosedT{
    always all t: Tournament | isClosedT[t] implies (all b: t.tBattles | isClosedB[b])
}

// An Open Tournament can only have open battle

fact CanBeClosedT{
    always all t: Tournament | isOpenT[t] implies (all b: t.tBattles | isOpenB[b])
}

// ------------------------------------- BATTLE FACTS

// battle status transitions

fact StateTransitionsB{
    always all b: Battle | isNotCreatedB[b] implies (isNotCreatedB[b] until isOpenB[b])
    always all b: Battle | isOpenB[b] implies (isOpenB[b] until isInProgressB[b])
    always all b: Battle | isInProgressB[b] implies (isInProgressB[b]until isClosedB[b])
    always all b: Battle | isClosedB[b] implies always isClosedB[b]
}

// Not yet created battle can't be linked to Tournaments

fact NotCreatedBattle{
    always all b: Battle | isNotCreatedB[b] implies !(some t: Tournament | b in t.tBattles)
}

// Created Battle must be linked to a Tournament
fact CreateBattleInTournament{
    always all b: Battle | !isNotCreatedB[b] implies (some t: Tournament | b in t.tBattles)
}

// Battle is consistent with specifics

fact ConsistentBattle{
    always all b: Battle | b.minSize > 0 && b.minSize <= b.maxSize
}


// --------------------------------- TEAM FACTS

// team status transitions

fact StateTransitionsTeam{
    always all t: Team | isCreatedTeam[t] implies (always isCreatedTeam[t])
}

// Team not created, doesn't have members or linked in a battle

fact NotCreatedTeam{
    always all t: Team | !isCreatedTeam[t] implies #t.members = 0
    always all t: Team | !isCreatedTeam[t] implies !(some b: Battle | t in b.bTeams)
}

// Created Team have correct size and at least one memeber

fact CreatedTeam{
    always all t: Team | isCreatedTeam[t] implies #t.members > 0
    always all t: Team | isCreatedTeam[t] implies (all b: Battle| t in b.bTeams implies (t.size >= b.minSize && t.size <= b.maxSize && #t.members >= b.minSize))
    always all t: Team | isCreatedTeam[t] implies (one b: Battle | t in b.bTeams)
}


// team in the same battle can't have equal members

fact StudentInOneTeam{
    always all b: Battle, t1, t2: b.bTeams | t1 != t2 implies (all s1: t1.members, s2: t2.members | s1 != s2)
}

// Consistency of team

fact ConsistencyTeam{
    always all t: Team, s: Student | once s in t.members implies always s in t.members 
    always all t: Team, tourn: Tournament, b: tourn.tBattles | t in b.bTeams implies (all s: t.members | s in tourn.participants)
    always all t: Team | t.size > 0 && #t.members <= t.size
    always all t: Team, b: Battle | once t in b.bTeams implies always t in b.bTeams
}

// Score of Team

fact TeamScore{
    always all b: Battle, t: b.bTeams | isOpenB[b] implies t.score = 0
    always all b: Battle, t: b.bTeams | (isClosedB[b] || isInProgressB[b]) implies t.score >= 0
}

// -------------------------------------- SCORE FACTS


// Not created score must not be associated with Students, and not be in any Tournament

fact NotCreatedScore{
    always all s: Score | !isCreatedS[s] implies (#s.student = 0 && !(some t:Tournament| s in t.leaderBoard))
}

// Created Score are always associated with a Student and a Tournament

fact CreatedScore{
    always all s: Score | isCreatedS[s] implies (always isCreatedS[s])
    always all s: Score | isCreatedS[s] implies (#s.student = 1 && (one t: Tournament | s in t.leaderBoard && s.student in t.participants))
}

// A score can't be associated with two tournaments
// Dato disj set potrebbe non servire

fact OnlyOneTournament{
    always all t1, t2: Tournament, s1: t1.leaderBoard, s2: t2.leaderBoard | t1 != t2 implies s1 != s2
}

// A student in a Tournament can't have two Score associated

fact OnlyOneScore{
    always all t: Tournament, s1, s2: t.leaderBoard | s1 != s2 implies s1.student != s2.student
}

// Consistency of Score

fact ScoreConsistency{
    always all s: Student, score: Score | once s = score.student implies always s = score.student
    always all t: Tournament, score: Score | once score in t.leaderBoard implies always score in t.leaderBoard
}

// All students in a Tournament must have a score

fact ScoreInTournament{
    always all t: Tournament | #t.participants = #t.leaderBoard
}


// Score values must be non negative

fact NonNegativeScore{
    always all s: Score | s.value >= 0
}

// All ranks are in order given their score

fact ranksAreInSuccession {
    always all t: Tournament, s: t.leaderBoard | (isInProgressT[t] || isClosedT[t]) implies (s.rank > 0 and s.rank <= #t.leaderBoard)
    always all t: Tournament, s1, s2: t.leaderBoard | (isInProgressT[t] || isClosedT[t]) implies (s1 != s2 implies s1.rank != s2.rank)
    always all t: Tournament | (isInProgressT[t] || isClosedT[t]) implies lone s: t.leaderBoard | s.rank = 1
    always all t: Tournament | (isInProgressT[t] || isClosedT[t]) implies lone s: t.leaderBoard | s.rank = #t.leaderBoard
}

//For every two students in the participant sets, a student with a higher score in a tournament has a lower rank

fact studentsWithHigherScoreHaveLowerRank{
    always all t: Tournament, s1, s2: t.leaderBoard | (s1 != s2 and (isInProgressT[t] || isClosedT[t])) implies ((s1.value >= s2.value iff s1.rank <= s2.rank)) //and (s1.value = s2.value implies s1.rank = s2.rank))

}

// Scores are equal to 0 while Tournament is Open

fact NoPointsAtStart{
    always all t: Tournament, s: t.leaderBoard | isOpenT[t] implies (s.value = 0 && s.rank = 0)
}

// ------------------------ BADGE FACTS

// Participation Badge fact
fact participationBadgeConsistency{
    always all t: Tournament | ParticipationBadge in t.tBadges implies (all s: t.participants | ParticipationBadge in s.sBadges)
    always all s: Student | ParticipationBadge in s.sBadges implies (some t: Tournament | ParticipationBadge in t.tBadges && s in t.participants)
}

// Participatino Badge fact
fact teamBadgeConsistency{
    always all t: Tournament | TeamBadge in t.tBadges implies (all b: t.tBattles, team: b.bTeams | #team.members > 1 implies (all s: team.members | TeamBadge in s.sBadges))
    always all s: Student | TeamBadge in s.sBadges implies (some t: Tournament, b: t.tBattles, team: b.bTeams | TeamBadge in t.tBadges && s in t.participants && s in team.members && #team.members > 1)
}

// Double Digit Score Badge fact
fact DoubleDigitScoreConsistency{
    always all t: Tournament | DoubleDigitScoreBadge in t.tBadges implies (all score: t.leaderBoard | score.value > 9 implies DoubleDigitScoreBadge in score.student.sBadges)
    always all s: Student | DoubleDigitScoreBadge in s.sBadges implies (some t: Tournament, score: t.leaderBoard | DoubleDigitScoreBadge in t.tBadges && score.value > 9 and s = score.student)
}

// ---------------------------------------------------------- PRED SECTION -----------------------------------------



// ------------------------ USER PRED

// Predicates to check User Status

pred isSigned[u: User]{
    u.uStatus = Signed
}

// Users can be added to the model dynamically

pred addUser[u: User]{
    //pre-condition
    u.uStatus = NotSigned
    //post-condition
    u.uStatus' = Signed
}

pred TestUser{
    some u: User | addUser[u]
}

// ------------------------ TOURNAMENT PRED

// Predicates to chek tournament State

pred isOpenT[t: Tournament]{
    t.tStatus = OpenT
}

pred isClosedT[t: Tournament]{
    t.tStatus = ClosedT
}

pred isInProgressT[t: Tournament]{
    t.tStatus = InProgressT
}

pred isNotCreatedT[t: Tournament]{
    t.tStatus = NotCreatedT
}

// Tournament can be created

pred CreateTorunament[t: Tournament, e: Educator, b: set BadgeType]{
    //pre-condition
    t.tStatus = NotCreatedT
    //post-condition
    t.tStatus' = OpenT
    t.administrators' = t.administrators + e
    t.tBadges' = t.tBadges + b
}

// Administrators can add other addministrators

pred AddAdministrator[t: Tournament, e: Educator]{
    //pre-condition
    t.tStatus != NotCreatedT
    t.tStatus != ClosedT
    //post-condition
    t.administrators' = t.administrators + e
}

// Add a student to a Tournament

pred addStudentToTourn[t: Tournament, s: Student, score: Score]{
    //pre-condition
    t.tStatus = OpenT
    s.uStatus = Signed
    !isCreatedS[score]
    //post-condition
    t.participants' = t.participants + s
    score.sStatus' = CreatedS
    score.student' = s
    t.leaderBoard' = t.leaderBoard + score

}

// Add a battle to a Torunament

pred addBattleToTourn[t: Tournament, b: Battle]{
    //pre-condition
    (t.tStatus = OpenT || t.tStatus = InProgressT) 
    b.bStatus = NotCreatedB
    //post-condition
    t.tBattles' = t.tBattles + b
    b.bStatus' = OpenB
}

pred TestTournament{
    some t: Tournament, s: Student, score: Score | addStudentToTourn[t, s, score]
    some t: Tournament, e: Educator, b: set BadgeType | CreateTorunament[t, e, b]
    some t: Tournament, e: Educator | (!(e in t.administrators) && AddAdministrator[t, e])
    some t: Tournament, b: Battle | addBattleToTourn[t, b]
}

// ----------------------------- BATTLE PRED

// Predicates to check battle status

pred isNotCreatedB[b: Battle]{
    b.bStatus = NotCreatedB
}

pred isOpenB[b: Battle]{
    b.bStatus = OpenB
}

pred isInProgressB[b: Battle]{
    b.bStatus = InProgressB
}

pred isClosedB[b: Battle]{
    b.bStatus = ClosedB
}

// ---------------------------- TEAM PRED

// Predicates to check status

pred isCreatedTeam[t: Team]{
    t.teamStatus = CreatedTeam
}

// Create a team

pred createTeam[t: Team, b: Battle, tourn: Tournament, s: set Student]{
    //pre-condition
    t.teamStatus = NotCreatedTeam
    b.bStatus = OpenB
    b in tourn.tBattles
    #s >= b.minSize
    #s <= t.size
    !(some team: b.bTeams | s in team.members)
    s in tourn.participants
    //post-condition
    t.members' = t.members + s
    b.bTeams' = b.bTeams + t
    b.bStatus' = OpenB
    t.teamStatus' = CreatedTeam
}

// Add a member to a Team

pred joinTeam[t: Team, b: Battle, tourn: Tournament, s: Student]{
    //pre-condition
    t.teamStatus = CreatedTeam
    b.bStatus = OpenB
    b in tourn.tBattles
    t in b.bTeams
    s in tourn.participants
    #t.members < t.size
    //post-condition
    t.members' = t.members + s
    b.bStatus' = OpenB
}


pred TestTeam{
    some t: Tournament, b: Battle, s: set Student, team: Team | createTeam[team, b, t, s]
    some t: Tournament, b: t.tBattles, s: t.participants, team: b.bTeams | joinTeam[team, b, t, s]
}

// ----------------------------------- SCORE PRED

pred isCreatedS[s: Score]{
    s.sStatus = CreatedS
}


// Used to check for some properties

fact{
    //always some t: Tournament | #t.participants > 1
    some t: Tournament | #t.tBadges > 0
    some t: Tournament | TeamBadge in t.tBadges && (some s: t.participants | TeamBadge in s.sBadges)
    some s: Student | ParticipationBadge in s.sBadges
    some s: Student | DoubleDigitScoreBadge in s.sBadges
}



pred show{
    TestTournament
    TestUser
    TestTeam
}

run show for 4 but 6 Int, 10 User