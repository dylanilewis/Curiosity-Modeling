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
    some disj p1, p2 :Player | 
    p1 in r.players 
    p2 in r.players
    #(r.players) = 2
    r = postRiver
    p1.hand.score > p2.hand.score
}

pred badWinnerRoundState[r: RoundState]{
    some disj p1, p2 :Player | 
    p1 in r.players 
    p2 in r.players
    #(r.players) = 2
    r = postRiver
    p1.chips = p2.chips + r.pot
}


test suite for winner {

}


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


