/*
sig -> torneo, battle, user {a}, student {student_in_tournament}, educator, (guest?), badge, team

requirements

*/


// Alloy model for CodeKataBattle platform - Entities and Facts

// Signatures
abstract sig User{
    username: one Int
}


sig Student extends User{

    //subscribedTournaments: set Tournament,
    //participatedBattles: set Battle
    //badges: set Badge,
}


sig Educator extends User{

}

sig Score{
    student: one Student,
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

fact uniquesername{
    all u1, u2: User | u1!=u2 implies u1.username != u2.username
}

// ------------------------- TOURNAMENT RELATED FACTS

//For every two students in the participant sets, a student with a higher score in a tournament has a lower rank

fact studentsWithHigherScoreHaveLowerRank{
    all t: Tournament, s1, s2: t.leaderboard | s1 != s2 implies ((s1.value >= s2.value iff s1.rank <= s2.rank)) //and (s1.value = s2.value implies s1.rank = s2.rank))

}

// A score is linked to a torunament ALWAYS!!!!!!!!

fact scoreLinkedTournament{
    all score: Score | some tournament: Tournament | score in tournament.leaderboard
}

// A score can't be in two different tournaments

fact noDoubleScore{
    all t1, t2: Tournament, s1: t1.leaderboard, s2: t2.leaderboard|t1!=t2 implies s1 != s2
    
}


// Links the score in the tournament with the participants in the same tournament

fact studentInTournamentMatchesScore {
    all t: Tournament | t.participants = (t.leaderboard.student)
}

// In a tournament, a student is linked to only one score

fact singleStudentScore{
    all tournament: Tournament, s1, s2: tournament.leaderboard | s1 != s2 implies s1.student != s2.student
}


// Tournament needs to have at least one administrator

fact numAdministrators{
    all t: Tournament | #t.administrators > 0
}

// ---------------------- TEAM RELATED FACTS
// Just some general variable check

fact generalTeamReq{
    all team: Team | #team.members <= team.size and team.size > 0 and team.score >= 0 and #team.members > 0
    
}

// The size defined for the team must be in battle constraint and Num of members is at least minimum in a team

fact correctSize{
    all battle: Battle, team: battle.teams | team.size >= battle.min_size and team.size <= battle.max_size and #team.members >= battle.min_size
}

// The students in a team must be all relative to the same tournament

fact possibleTeam{
    all t: Tournament, b: t.battles, team : b.teams, m: team.members | m in t.participants 
}

// Teams must be linked to a battle

fact teamBattleRel{
    all team: Team| one battle: Battle | team in battle.teams
}

// Students in a battle must be in only one team

fact oneTeamPerStudent{
    all battle: Battle, team1, team2: battle.teams | team1 != team2 implies (all s1: team1.members, s2: team2.members | s1 != s2)
}

// ----------------------- BATTLE RELATED FACTS

fact generalBattleReq{
    all battle: Battle | battle.min_size <= battle.max_size and battle.min_size > 0
}

// Battle are related to tournament

fact battleTournamentRel{
    all battle: Battle | one tournament: Tournament | battle in tournament.battles
}

// ----------------------- SCORE RELATED FACTS

// general req

fact generalScoreReq{
    all score: Score | score.value >= 0 and score.rank > 0
}

/*
fact gg{
    all s1, s2: Score | s1 != s2 implies s1.value != s2.value
}
*/

fact ranksAreInSuccession {
    all t: Tournament, s: t.leaderboard | s.rank > 0 and s.rank <= #t.leaderboard
    all t: Tournament, s1, s2: t.leaderboard | s1 != s2 implies s1.rank != s2.rank
    all t: Tournament | lone s: t.leaderboard | s.rank = 1
    all t: Tournament | lone s: t.leaderboard | s.rank = #t.leaderboard
}
/*
fact firstExists{
    //all tournament: Tournament | some score : tournament.leaderboard | score.rank = 1
}
*/
/*
// HARD SUPER UPER HARD CONSTRAINT
// FOR EVERY TOURNAMENT, PEOPLE IN THE BATTLES MUST BE THE SAME PEOPLE IN THE TOURNAMENT

fact consistencyBattleTorunament{
    // TO-DO
}




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

pred show{
}

run show for 4 but exactly 10 Student, exactly 4 Battle, exactly 2 Tournament, exactly 1 Educator, exactly 4 Score, exactly 4 Team