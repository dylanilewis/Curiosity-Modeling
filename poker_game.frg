#lang forge/bsl

abstract sig RoundState {
    // the state of the game
    players: set Player,
    deck: set Card,
    board: set Card,
    pot: int,
    highestBet: int,
}   

// states of the game
one sig preFlop, postFlop, postTurn, postRiver extends RoundState {}

sig Suit {
    // the suit of the card
    suit: one of Spades, Hearts, Diamonds, Clubs,
}

sig Value {
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
    cards: set Card,
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

// better to have many seperate types of chips defined in sig or have them just all be int's? something to figure out before coding init.
sig Chip {
    // the chips
    amount: int,
}

pred initRound {
    // Implement logic for initializing the round
    nextRound
    dealCards
}

// need to figure out how to make dealer do the actions associated with each state
pred nextRoundState {
    // Implement logic for transitioning to the next state
    all p : Player | r : RoundState | (p.bet = r.highestBet) {
        #(r.players) = 1 implies findRoundWinner
        r = preFlop implies r = postFlop
        r = postFlop implies r = postTurn
        r = postTurn implies r = postRiver
    }
}

pred dealCards {
    // Implement logic for dealing the cards
    all p : Player | all r : RoundState | (r = preFlop) and (#p.hand < 2) {
        p.hand = p.hand + r.deck.first
        r.deck = r.deck - r.deck.first
    }
}

pred playerFolds {
    // Implement logic for player folding
    some p : Player | some r : RoundState | {
        r.players = r.players - p
    }
}

pred playerChecks {
    // Implement logic for player checking
    some p : Player | some s : RoundState | (p.bet = s.highestBet) {
        p.bet = p.bet
    }
}

pred playerCalls {
    // Implement logic for player calling
    some p : Player | some s : RoundState | (p.chips.amount > 0) {
        p.bet = s.highestBet
        p.chips.amount = p.chips.amount - s.highestBet + p.bet
        s.pot = s.pot + s.highestBet - p.bet
    }
}

pred playerRaises {
    // Implement logic for player raising
    some p : Player | some s : RoundState | some i : Int | (p.chips.amount > 0) and (i > s.highestBet) {
        p.bet = i
        p.chips.amount = p.chips.amount - i
        s.pot = s.pot + i
        s.highestBet = i
    }
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
    some p : Player | some r : RoundState | {
        r.players = r.players - p
    }
}

pred hasPair {
    //see if a player has a pair in his hand
    some r : RoundState | some p : Player | some value : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value) = 2
    }
    not hasTwoPair and not hasThreeofaKind and not hasFullHouse
}

pred hasTwoPair{
    some r : RoundState | some p : Player | some value1, value2 : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value1) = 2 and #(hand.card.value = value2) = 2
    }
}

pred hasFullHouse{
    hasThreeofaKind and hasPair
}

pred hasStraight{
    some r : RoundState | some p : Player | some v1, v2, v3, v4, v5 : Value | {
        hand = r.board + p.hand
        (v1 = v2 + 1) and (v2 = v3 + 1) and (v3 = v4 + 1) and (v4 = v5 + 1)
    }
}

pred hasFlush{
    some r : RoundState | some p : Player | some suit : Suit | {
        hand = r.board + p.hand
        #(hand.card.Suit = suit) = 5
    }
}

pred hasRoyalFlush{
    some r : RoundState | some p : Player | some v1, v2, v3, v4, v5 : Value | {
        hasStraightFlush
        hand = r.board + p.hand
        hand.Card.v1 = Ace
        hand.Card.v2 = King
        hand.Card.v3 = Queen
        hand.Card.v4 = Jack
        hand.Card.v5 = Ten
    }
}

pred hasFourOfaKind{
    some r: RoundState | some p: Player | some value1 : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value1) = 4
    }
}

pred hasThreeofaKind{
    some r: RoundState | some p: Player | some value1 : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value1) = 3
    }
    not hasPair and not hasFullHouse
}

pred hasStraightFlush {
    hasStraight and hasFlush and not RoyalFlush
}

pred evaluateHand {
    // Implement logic for evaluating the hand
}

pred findRoundWinner {
    // Implement logic for finding the round winner
    /*
    for loop through players calling evaluate hand. Whoever has the highest value wins, pot goes to them.
    */
}