#lang forge

open "poker_game.frg"

pred dealCardsTest1{
    all p: Player | some disj c1, c2: Card{
        p.hand.cards = c1 + c2
    }
}

pred dealCardsTest2{
    all p: Player | some c1, c2: Card {
        c1 = c2
        p.hand.cards = c1 + c2
    }
}

pred dealCardsTest3{
    all p: Player | some c1, c2, c3: Card{
        p.hand.cards = c1 + c2 + c3
    }
}
test suite for dealCards {
    test expect {
        t1: {dealCardsTest1 and dealCards} is sat
        t2: {dealCardsTest2 and dealCards} is unsat
        t3: {dealCardsTest3 and dealCards} is unsat
    }
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


