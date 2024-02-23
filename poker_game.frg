#lang forge/bsl

abstract sig State {
    // the state of the game
    players: set Player,
    remainingDeck: set Card,
    board: set Card,
    pot: int,
}

// states of the game
one sig preFlop, postFlop, postTurn, postRiver extends State {}

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

one sig SmallBlind, BigBlind, Regular extends Position {}

sig Chip {
    // the chips
    amount: int,
}