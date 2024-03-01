#lang forge

abstract sig RoundState {
    // the state of the game
    players: set Player,
    deck: set Card,
    board: set Card,
    pot: one Int,
    highestBet: one Int,
    turn: one Player,
    next: lone RoundState
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

pred dealCards {
    all p : Player | {
        #(p.hand.cards) = 2
    }
}

pred initRound[r : RoundState] {
    // Implement logic for initializing the round
    r.board = none
    dealCards
    one p : Player | {
        p = r.turn
    }
}

pred winner[r : RoundState] {
    // Implement logic for finding the winner
    some p : Player {
        ((#(r.players) = 1) and (p in r.players)) or {
            all disj p1, p2 : Player | {
                r = postRiver
                p1.hand > p2.hand
            }
        }
    }
}

pred validTurn[r : RoundState] {
    canPlay[r] implies playerAction[r] else playerFolds
    r.turn = r.turn.nextPlayer
}

pred validTransition[pre: RoundState, post: RoundState] {
    all p : Player | {
        validTurn[pre]
    }
    pre = preFlop implies post = postFlop
    pre = postFlop implies post = postTurn
    pre = postTurn implies post = postRiver
}

pred canPlay[r : RoundState] {
    some p: Player | {
        r.turn = p 
        p in r.players
        p.chips > 0 or p.bet = r.highestBet
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
    some p : Player | some s : RoundState | {(p.bet = s.highestBet) {
        p.bet = p.bet
    }}
}

pred playerCalls {
    // Implement logic for player calling
    some p : Player | some s : RoundState | {(p.chips > 0) {
        p.bet = s.highestBet
        p.chips = p.chips - s.highestBet + p.bet
        s.pot = s.pot + s.highestBet - p.bet
    }}
}

pred playerRaises {
    // Implement logic for player raising
    some p : Player | some s : RoundState | some i : Int | {(p.chips > 0) and (i > s.highestBet) {
        p.bet = i
        p.chips = p.chips - i
        s.pot = s.pot + i
        s.highestBet = i
    }}
}

pred playerAllIns {
    // Implement logic for player going all in
    some p : Player | some s : RoundState | {(p.chips > 0) {
        p.bet = p.bet + p.chips
        p.chips = 0
        s.pot = s.pot + p.bet
    }}
}

pred playerAction[r : RoundState] {
    playerChecks or playerCalls or playerRaises or playerAllIns
}

pred traces {
    one preFlop, postRiver: RoundState | {
        winner[postRiver]
        initRound[preFlop]
        all r : RoundState | {
            -- all states are reachable from the initial state
            r != preFlop implies reachable[r, preFlop, next]
            -- all of the transitions between initial to final state are valid
            some r.next implies validTransition[r, r.next]
        }
    }
    all r : RoundState | {
        winner[r] implies not some r.next
    }
}

pred uniqueCards {
    all disj c1, c2 : Card | {
        not (c1.rank = c2.rank and c1.suit = c2.suit)
    }
}

pred wellformedDeck {
    uniqueCards
    
}

pred playerRotation {
    all p1, p2 : Player | {
        reachable[p1, p2, nextPlayer]
    }
}


pred hasPair[p : Player] {
    some r : RoundState | some rank : Rank | {
        hand = r.board + p.hand
        #(hand.Card.value = rank.value) = 2
    }
}

pred hasTwoPair[p : Player] {
    some r : RoundState | some rank1, rank2 : Rank | {
        hand = r.board + p.hand
        #(hand.Card.value = rank1.value) = 2 and #(hand.Card.value = rank2.value) = 2
    }
}

pred hasFullHouse[p : Player] {
    hasThreeofaKind[p] and hasPair[p]
}

pred hasStraight[p : Player] {
    some r : RoundState | some r1, r2, r3, r4, r5 : Rank | {
        hand = r.board + p.hand
        (r1.value = r2.value + 1) and (r2.value = r3.value + 1) and (r3.value = r4.value + 1) and (r4.value = r5.value + 1)
    }
}

pred hasFlush[p : Player] {
    some r : RoundState | some suit : Suit | {
        hand = r.board + p.hand
        #(hand.Card.Suit = suit) = 5
    }
}

pred hasRoyalFlush[p : Player] {
    some r : RoundState | some r1, r2, r3, r4, r5 : Rank | {
        hasStraightFlush[p]
        hand = r.board + p.hand
        hand.Card.r1.value = Ace
        hand.Card.r2.value = King
        hand.Card.r3.value = Queen
        hand.Card.r4.value = Jack
        hand.Card.r5.value = Ten
    }
}

pred hasFourOfaKind[p : Player] {
    some r: RoundState | some rank1 : Rank | {
        hand = r.board + p.hand
        #(hand.Card.rank.value = rank1.value) = 4
    }
}

pred hasThreeofaKind[p : Player] {
    some r: RoundState | some rank1 : Rank | {
        hand = r.board + p.hand
        #(hand.Card.value = rank1.value) = 3
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

pred evaluateHand[p : Player] {
    // Implement logic for evaluating the hand
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

pred handRanks {
    HighCard.value = 1
    Pair.value = 2
    TwoPair.value = 3
    ThreeOfaKind.value = 4
    Straight.value = 5
    Flush.value = 6
    FullHouse.value = 7
    FourOfaKind.value = 8
    StraightFlush.value = 9
    RoyalFlush.value = 10
}

run {
    wellformedDeck
    playerRotation
    // traces
    } for exactly 52 Card, 3 Player