#lang forge/bsl

open "poker_game.frg"


pred checkingPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    //want to say something like his bet doesnt increase but its hard because i feel
    //like i need to have something to track the previous turn maybe?
}

test suite for playerChecks {
    some p: Player | some s : RoundState |
    p in s.players
    s.highestBet = p.bet

}
pred foldingPlayer {
    some p: Player | some s : RoundState | 
    not p in s.players
}

test suite for playerFolds {
}
pred raisingPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    p.bet > s.highestBet
}
test suite for playerRaises {
    
}
pred callingPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    p.bet = s.highestBet
}

test suite for playerCalls {
    
}
pred allInPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    p.bet = p.stack
}
test suite for playerAllIns{
    
}


