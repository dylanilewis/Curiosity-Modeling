// file for game/actual stuff to happen

abstract sig State {
    // the state of the game
    players: set Player,
    remainingDeck: set Card,
    board: set Card,
}

// states of the game
one sig preFlop, postFlop, postTurn, postRiver extends State {}

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
}

sig Chip {
    // the chips
    value: int,
}