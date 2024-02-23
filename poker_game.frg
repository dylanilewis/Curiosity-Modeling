#lang forge/bsl

sig GameState {
    // the state of the game
    players: set Player,
    roundState: RoundState,
}

abstract sig RoundState {
    // the state of the game
    players: set Player,
    remainingDeck: set Card,
    board: set Card,
    pot: int,
    highestBet: int,
}   

// states of the game
one sig preFlop, postFlop, postTurn, postRiver extends RoundState {}

sig suit {
    // the suit of the card
    suit: one of Spades, Hearts, Diamonds, Clubs,
}

sig value {
    // the value of the card
    value: one of Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten, Jack, Queen, King, Ace,
}

sig Card {
    // the card
    suit: suit,
    value: value,
}

sig Hand {
    // the hand of a player
    cards: set card,
}

sig Player {
    // the player
    hand: Hand,
    chips: set Chip,
    bet: int,
    position: Position,
}

abstract sig Position {
    // the position of the player
    ante: int,
}

// need to figure out how to set players to each position and rotate them through the game. maybe add a position field to player sig?
one sig SmallBlind, BigBlind, Regular extends Position {}

sig Chip {
    // the chips
    amount: int,
}

pred init {
    // Implement logic for initializing the game
}

pred nextRoundState {
    // Implement logic for transitioning to the next state
}

pred nextRound {
    // Implement logic for transitioning to the next round
}

pred dealCards {
    // Implement logic for dealing the cards
}

pred playerFolds {
    // Implement logic for player folding
}

pred playerCanCheck[player: Player, roundState: RoundState] {
    // Implement logic for checking if the player can check
}

pred playerChecks {
    // Implement logic for player checking
    some p : Player | some s : RoundState | (playerCanCheck[p, s]) {
        p.bet = p.bet
    }
}

pred playerBets {
    // Implement logic for player betting
}

pred playerCalls {
    // Implement logic for player calling
}

pred playerRaises {
    // Implement logic for player raising
}

pred playerAllIns {
    // Implement logic for player going all in
    some p : Player | some s : RoundState | (p.chips.amount > 0) {
        p.bet = p.bet + p.chips.amount
        p.chips.amount = 0
        s.pot = s.pot + p.bet
    }
}

pred playerLeaves {
    // Implement logic for player leaving the game
    some p : Player | some s : GameState | {
        s.players = s.players - p
    }
}

pred evaluateHand {
    // Implement logic for evaluating the hand
}

pred findRoundWinner {
    // Implement logic for finding the round winner
}

pred isRoundFinished {
    // Implement logic for checking if the round is finished
}

pred isGameFinished {
    // Implement logic for checking if the game is finished
}