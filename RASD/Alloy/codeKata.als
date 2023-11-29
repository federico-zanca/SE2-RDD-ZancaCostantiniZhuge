// Alloy model for CodeKataBattle platform - Entities and Facts

// Signatures
abstract sig User {
    id: Int,
}

sig Student extends User {
    subscribedTournaments: set Tournament,
    participatedBattles: set Battle,
    scores: set Score,
    badges: set Badge
}
sig Educator extends User {}

sig Tournament {
    battles: set Battle,
    scores: set Score,
    badges: set Badge
}

sig Battle {
  participants: set Student,
  teams: set Student,
  repository: one GitHubRepository,
  deadline: Int, //replace with Date sig?
  codeKata: one CodeKata,
  scores: set Score
}

sig GitHubRepository {
    codeKata: one CodeKata
}

sig CodeKata {
    description: String,
    // Gradle Project? Software Project including Gradle Project + testCases?
    testCases: set TestCase
}

sig TestCase {
    provided_input: String,
    expected_output: String
}

sig Score {
    student: one Student,
    battle: one Battle,
    functionalAspects: Int,
    timeliness: Int,
    qualityLevel: Int,
    optionalScore: Int
}

sig Badge {
    title: String,
    rules: BadgeRules
}

abstract sig BadgeRules {}

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
