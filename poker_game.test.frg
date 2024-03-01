#lang forge

open "poker_game.frg"

pred dealCardsTest1{
    all p: Player | some disj c1, c2: Card | some disj i1, i2: Int{
        (p.hand.cards[i1]) = c1
        (p.hand.cards[i2]) = c2
    }
}

pred dealCardsTest2{
    all p: Player | some c1, c2: Card | some disj i1, i2: Int{
        c1 = c2
        (p.hand.cards[i1]) = c1
        (p.hand.cards[i2]) = c2
    }
}

pred dealCardsTest3{
    all p: Player | some c1, c2, c3: Card | some disj i1, i2, i3: Int{
        (p.hand.cards[i1]) = c1
        (p.hand.cards[i2]) = c2
        (p.hand.cards[i3]) = c3
    }
}
test suite for dealCards {
    test expect {
        t1: {dealCardsTest1 and dealCards} is sat
        t2: {dealCardsTest2 and dealCards} is unsat
        t3: {dealCardsTest3 and dealCards} is unsat
    }
}

pred playersChipsGood{
    all p: Player | p.chips = 5
}

pred playersChipsBad{
    one p: Player | p.chips = 3
}

pred playerBadBet{
    one p: Player | p.bet = 3
}

pred playerGoodBet{
    all p: Player | p.bet = 0
}

pred goodRoundState[s: RoundState]{
    s.highestBet = 0
    s.board = none
    s.highestBet = 0
    s.pot = 0
}

pred badRoundState[s: RoundState]{
    s.highestBet = 3
    s.board = none
    s.highestBet = 0
    s.pot = 0
}

test suite for initRound{
    test expect {
        t11: {some r: RoundState | playersChipsGood and goodRoundState[r] and initRound[r]} is sat
        t22: {some r: RoundState | playersChipsBad and goodRoundState[r] and initRound[r]} is unsat
        t33: {some r: RoundState | playersChipsGood and badRoundState[r] and initRound[r]} is unsat
    }
}

pred winnerRoundState1Player[r: RoundState]{
    one p1 :Player | p1 in r.players and #(r.players) = 1
    r = postRiver
}
pred winnerRoundState2Players[r: RoundState]{
    some disj p1, p2 :Player | {
    p1 in r.players 
    p2 in r.players
    #(r.players) = 2
    r = postRiver
    p1.hand.score > p2.hand.score
    }
}

pred badWinnerRoundState[r: RoundState]{
    some disj p1, p2 :Player | {
    p1 in r.players 
    p2 in r.players
    #(r.players) = 2
    r = postRiver
    p1.chips = p1.chips + r.pot
    p2.hand.score > p1.hand.score
    }
}


test suite for winner {
    test expect {
        t1winner: {some r: RoundState | winnerRoundState1Player[r] and winner[r]} is sat
        t2winner: {some r: RoundState | winnerRoundState2Players[r] and winner[r]} is sat
        t3winner: {some r: RoundState | badWinnerRoundState[r] and winner[r]} is unsat
    }
}
pred canPlay1[r: RoundState]{
    some p: Player | {
    p in r.players
    p.chips > 0
    r.turn = p
    }

}

pred notHisTurn[r: RoundState]{
    some p: Player | {
    p in r.players
    r.turn != p
}}

pred notInPlayers[r: RoundState]{
    some p: Player | not p in r.players
}

pred notEnoughChips[r: RoundState]{
    some p: Player | {
    p in r.players
    p.chips = 0
}}

test suite for canPlay {
    test expect {
        t1: {some r: RoundState | canPlay1[r] and canPlay[r]} is sat
        t2: {some r: RoundState | notHisTurn[r] and canPlay[r]} is unsat
        t3: {some r: RoundState | notInPlayers[r] and canPlay[r]} is unsat
        t4: {some r: RoundState | notEnoughChips[r] and canPlay[r]} is unsat
    }
}

pred validTurn1[r: RoundState]{
    some p: Player | {
    p in r.players
    p.bet = r.highestBet
}}

pred notValidTurn1[r: RoundState]{
    some p: Player |{
    p in r.players
    p.bet > r.highestBet
}}

test suite for validTurn {
    assert canPlay is necessary for validTurn
    test expect {
        t1: {some r: RoundState | canPlay1[r] and validTurn[r]} is sat
        t2: {some r: RoundState | notHisTurn[r] and validTurn[r]} is unsat
        t3: {some r: RoundState | notInPlayers[r] and validTurn[r]} is unsat
        t4: {some r: RoundState | notEnoughChips[r] and validTurn[r]} is unsat
        t5: {some r: RoundState | notValidTurn1[r] and validTurn[r]} is unsat
    }
}

pred preFlopToPostFlop[pre, post: RoundState]{
    some disj c1, c2, c3: Card | some disj i1, i2, i3: Int {
    pre = preFlop
    pre.next = post
    post = postFlop
    pre.board = none
    #(post.board) = 3
}}

pred postFlopToPostTurn[pre, post: RoundState]{
    pre = postFlop
    pre.next = post
    post = postTurn
    pre.board = post.board
    #(post.board) = 4
}

pred postTurnToPostRiver[pre, post: RoundState]{
    pre = postTurn
    pre.next = post
    post = postRiver
    pre.board = post.board
    #(post.board) = 5
}

// test suite for validTransition {
//     assert validTurn is necessary for validTransition
// }


// pred checkingPlayer {
//     some p: Player | some s : RoundState | 
//     p in s.players
//     //want to say something like his bet doesnt increase but its hard because i feel
//     //like i need to have something to track the previous turn maybe?
// }

// test suite for playerChecks {
//     some p: Player | some s : RoundState |
//     p in s.players
//     s.highestBet = p.bet

// }
// pred foldingPlayer {
//     some p: Player | some s : RoundState | 
//     not p in s.players
// }

// test suite for playerFolds {
// }
// pred raisingPlayer {
//     some p: Player | some s : RoundState | 
//     p in s.players
//     p.bet > s.highestBet
// }
// test suite for playerRaises {
    
// }
// pred callingPlayer {
//     some p: Player | some s : RoundState | 
//     p in s.players
//     p.bet = s.highestBet
// }

// test suite for playerCalls {
    
// }
// pred allInPlayer {
//     some p: Player | some s : RoundState | 
//     p in s.players
//     p.bet = p.stack
// }
// test suite for playerAllIns{
// }


