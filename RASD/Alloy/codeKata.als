/*
sig -> torneo, battle, user {a}, student {student_in_tournament}, educator, (guest?), badge, team

requirements

*/


// Alloy model for CodeKataBattle platform - Entities and Facts

// Signatures
abstract sig User {
    username: one String
}

sig Student extends User {
    //subscribedTournaments: set Tournament,
    //participatedBattles: set Battle
    //badges: set Badge,
}

sig Educator extends User {}

sig Score{
    student: one Student,
    tournament: one Tournament,
    value: Int,
    rank: Int
}


sig Team{
    members: disj set Student,
    size: Int,
    score: Int // Punteggio del team nella battle
}


sig Battle{
    teams: disj set Team,
    min_size: Int,
    max_size: Int
}


sig Tournament{
    participants: set Student,
    leaderboard: set Score,
    administrators: set Educator,
    battles: disj set Battle
}

// ------------------------ USER RELATED FACTS ------------------------

// Req: every user as an unique usernanme

fact uniqueUsername{
    all u1, u2: User | u1!=u2 implies u1.username != u2.username
}


// ------------------------- TOURNAMENT RELATED FACTS

//For every two students in the participant sets, a student with a higher score in a tournament has a lower rank

fact studentsWithHigherScoreHaveLowerRank{
    all t: Tournament, s1, s2: t.leaderboard | s1 != s2 implies (s1.value > s2.value implies s1.rank < s2.rank) and (s1.value = s2.value implies s1.rank = s2.rank)

}

// Links the score in the tournament with the participants in the same tournament

fact participantsInATournamentAreInLeaderboard{
    all t: Tournament, s: Student | s in t.participants implies one score: Score | score.student = s 
}

// Tournament needs to have at least one administrator

fact numAdministrators{
    all t: Tournament | #t.administrators > 0
}

// ---------------------- TEAM RELATED FACTS

// Just some general variable check

fact generalTeamReq{
    all team: Team | #team.members <= team.size and team.size > 0 and team.score >= 0
}

// ----------------------- BATTLE RELATED FACTS

fact generalBattleReq{
    all battle: Battle | battle.min_size >= battle.max_size and battle.min_size > 0
}

// There can't be a student in a battle being part of two differnt teams

fact oneTeamPerBattle{
    all battle: Battle, team1, team2: battle.teams | team1 != team2 implies (all s1: team1.members, s2: team2.members | s1 != s2)
}


// HARD SUPER UPER HARD CONSTRAINT
// FOR EVERY TOURNAMENT, PEOPLE IN THE BATTLES MUST BE THE SAME PEOPLE IN THE TOURNAMENT

fact consistencyBattleTorunament{
    // TO-DO
}





/*
fact numStudentsInATeamRespectsTeamSize{
    all t: Team | #t.members <= t.size and #t.members > 0  
}
*/




/*
// Facts and Constraints
fact UsersHaveUniqueIDs {
    all u1, u2: User | u1.id != u2.id
}

fact EachBattleHasUniqueRepository {
    all b1, b2: Battle | b1 != b2 implies b1.repository != b2.repository
}

fact EachCodeKataHasUniqueDescription {
    all ck1, ck2: CodeKata | ck1 != ck2 implies ck1.description != ck2.description
}

fact EachTestCaseHasUniqueDescription {
  all tc1, tc2: TestCase | tc1 != tc2 implies tc1.description != tc2.description
}

fact ScoresInRange {
  all s: Score | s.functionalAspects >= 0 and s.functionalAspects <= 100
  all s: Score | s.timeliness >= 0
  all s: Score | s.qualityLevel >= 0
  all s: Score | s.optionalScore >= 0
}

// Add more facts as needed...
*/