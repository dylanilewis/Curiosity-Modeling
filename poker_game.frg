#lang forge/bsl

abstract sig RoundState {
    // the state of the game
    players: set Player,
    deck: set Card,
    board: set Card,
    pot: one Int,
    highestBet: one Int,
    turn: one Player
}   

// states of the game
one sig preFlop, postFlop, postTurn, postRiver extends RoundState {}

sig Card {
    // the card
    suit: one Suit,
    rank: one Rank
}

abstract sig Suit {}
one sig Clubs, Diamonds, Hearts, Spades extends Suit {}

abstract sig Rank {
    value: one Int
}

one sig Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten, Jack, Queen, King, Ace extends Rank {}

sig Player {
    // the player
    hand: one Hand,
    chips: one Int,
    bet: one Int,
    nextPlayer: one Player
}

abstract sig Hand {
    // the hand of a player
    cards: pfunc Int -> Card
}

one sig RoyalFlush, StraightFlush, FourOfaKind, FullHouse, Flush, Straight, ThreeOfaKind, TwoPair, Pair, HighCard extends Hand {}

pred rankValues {
    Two.value = 2
    Three.value = 3
    Four.value = 4
    Five.value = 5
    Six.value = 6
    Seven.value = 7
    Eight.value = 8
    Nine.value = 9
    Ten.value = 10
    Jack.value = 11
    Queen.value = 12
    King.value = 13
    Ace.value = 14
}

// Sammy TODO: fix, should handle creating players, dealing cards, etc
pred initRound[r : RoundState] {
    // Implement logic for initializing the round
    r.board = none
    dealCards
    one p: Player |{
        p = r.turn
    }
}

// Sammy TODO: need to figure out how to make dealer do the actions associated with each state
pred nextRoundState {
    // Implement logic for transitioning to the next state
    all p : Player | all r : RoundState | (p.bet = r.highestBet) {
        #(r.players) = 1 implies findRoundWinner
        r = preFlop implies r = postFlop
        r = postFlop implies r = postTurn
        r = postTurn implies r = postRiver
    }
}

pred uniqueCards {
    all disj c1, c2 : Card | {
        not (c1.rank = c2.rank and c1.suit = c2.suit)
    }
}

pred playerRotation {
    all p1, p2 : Player | {
        reachable[p1, p2, nextPlayer]
    }
}

pred dealCards {
    all p : Player | {
        #{i : Int | p.hand[i]} = 2
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

pred hasPair[p : Player] {
    some r : RoundState | some value : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value) = 2
    }
}

pred hasTwoPair[p : Player] {
    some r : RoundState | some value1, value2 : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value1) = 2 and #(hand.card.value = value2) = 2
    }
}

pred hasFullHouse[p : Player] {
    hasThreeofaKind[p] and hasPair[p]
}

pred hasStraight[p : Player] {
    some r : RoundState | some v1, v2, v3, v4, v5 : Value | {
        hand = r.board + p.hand
        (v1 = v2 + 1) and (v2 = v3 + 1) and (v3 = v4 + 1) and (v4 = v5 + 1)
    }
}

pred hasFlush[p : Player] {
    some r : RoundState | some suit : Suit | {
        hand = r.board + p.hand
        #(hand.card.Suit = suit) = 5
    }
}

pred hasRoyalFlush[p : Player] {
    some r : RoundState | some v1, v2, v3, v4, v5 : Value | {
        hasStraightFlush[p]
        hand = r.board + p.hand
        hand.Card.v1 = Ace
        hand.Card.v2 = King
        hand.Card.v3 = Queen
        hand.Card.v4 = Jack
        hand.Card.v5 = Ten
    }
}

pred hasFourOfaKind[p : Player] {
    some r: RoundState | some value1 : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value1) = 4
    }
}

pred hasThreeofaKind[p : Player] {
    some r: RoundState | some value1 : Value | {
        hand = r.board + p.hand
        #(hand.card.value = value1) = 3
    }
}

pred hasStraightFlush[p : Player] {
    hasStraight[p] and hasFlush[p]
}

pred hasHighCard[p : Player] {
    not hasRoyalFlush[p]
    not hasStraightFlush[p]
    not hasFourOfaKind[p]
    not hasFullHouse[p]
    not hasFlush[p]
    not hasStraight[p]
    not hasThreeofaKind[p]
    not hasTwoPair[p]
    not hasPair[p]
}

pred evaluateHand {
    // Implement logic for evaluating the hand
    some p : Player | some r : RoundState | (r = postRiver) {
        hasRoyalFlush[p] implies p.hand = RoyalFlush
        hasStraightFlush[p] implies p.hand = StraightFlush
        hasFourOfaKind[p] implies p.hand = FourOfaKind
        hasFullHouse[p] implies p.hand = FullHouse
        hasFlush[p] implies p.hand = Flush
        hasStraight[p] implies p.hand = Straight
        hasThreeofaKind[p] implies p.hand = ThreeOfaKind
        hasTwoPair[p] implies p.hand = TwoPair
        hasPair[p] implies p.hand = Pair
        hasHighCard[p] implies p.hand = HighCard
    }
}

// pred findRoundWinner {
//     if (players.length == 1) {
//         players[0].chips.amount = players[0].chips.amount + RoundState.pot
//     } else {
//         int index = NegativeInfinity
//         int bestHand = 0
//         for each player : p in roundState.players {
//             if (evaluateHand[p] > bestHand) {
//                 bestHand = evaluateHand[p]
//                 index = p
//             } 
//         }
//         players[index].chips.amount = players[index].chips.amount + RoundStatepot
//     }
// }