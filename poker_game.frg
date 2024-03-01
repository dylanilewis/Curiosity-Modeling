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
    score: one Int,
    cards: func Int -> Card
}

one sig RoyalFlush, StraightFlush, FourOfaKind, FullHouse, Flush, Straight, ThreeOfaKind, TwoPair, Pair, HighCard extends Hand {}

// pred rankValues {
//     Two.value = -8
//     Three.value = -7
//     Four.value = -6
//     Five.value = -5
//     Six.value = -4
//     Seven.value = -3
//     Eight.value = -2
//     Nine.value = -1
//     Ten.value = 0
//     Jack.value = 1
//     Queen.value = 2
//     King.value = 3
//     Ace.value = 4
// }
/**
* This predicate maps the rank of cards to numeric values to make comparing cards easier 
*/
inst optimize_rank {
    Rank = `Two + `Three +`Four + `Five + `Six + `Seven + `Eight + `Nine + `Ten + `Jack + `Queen + `King + `Ace
    Two = `Two
    `Two.value = (-8)
    Three = `Three
    `Three.value = (-7)
    Four = `Four
    `Four.value = (-6)
    Five = `Five
    `Five.value = (-5)
    Six = `Six
    `Six.value = (-4)
    Seven = `Seven
    `Seven.value = (-3)
    Eight = `Eight
    `Eight.value = (-2)
    Nine = `Nine
    `Nine.value = (-1)
    Ten = `Ten
    `Ten.value = (0)
    Jack = `Jack
    `Jack.value = (1)
    Queen = `Queen
    `Queen.value = (2)
    King = `King
    `King.value = (3)
    Ace = `Ace
    `Ace.value = (4)

    Hand = `RoyalFlush + `StraightFlush + `FourOfaKind + `FullHouse + `Flush + `Straight + `ThreeOfaKind + `TwoPair + `Pair + `HighCard
    HighCard = `HighCard
    `HighCard.score = (-3)
    Pair = `Pair
    `Pair.score = (-2)
    TwoPair = `TwoPair
    `TwoPair.score = (-1)
    ThreeOfaKind = `ThreeOfaKind
    `ThreeOfaKind.score = (0)
    Straight = `Straight
    `Straight.score = (1)
    Flush = `Flush
    `Flush.score = (2)
    FullHouse = `FullHouse
    `FullHouse.score = (3)
    FourOfaKind = `FourOfaKind
    `FourOfaKind.score = (4)
    StraightFlush = `StraightFlush
    `StraightFlush.score = (5)
    RoyalFlush = `RoyalFlush
    `RoyalFlush.score = (6)
    
}

/**
* 
*/
pred dealCards {
    all p : Player | {
        #(p.hand.cards) = 2
    }
}

/**
* 
* Param: 
*/
pred initRound[r : RoundState] {
    // Implement logic for initializing the round
    r.board = none
    dealCards
    all p : Player | {
        p.bet = 0
        p.chips = 5
    }
    one p : Player | {
        p = r.turn
    }
}

/**
* 
* Param: 
*/
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

/**
* 
* Param: 
*/
pred validTurn[r : RoundState] {
    canPlay[r] implies playerAction[r] else playerFolds
    r.turn = r.turn.nextPlayer
}

/**
* 
* Param: 
* Param:
*/
pred validTransition[pre: RoundState, post: RoundState] {
    all p : Player | {
        validTurn[pre]
    }
    pre = preFlop implies {
        post = postFlop
        #(pre.board) = 0
        #(post.board) = 3
    }
    pre = postFlop implies {
        post = postTurn
        #(pre.board) = 0
        #(post.board) = 3
    }
    pre = postTurn implies {
        post = postRiver
        #(pre.board) = 0
        #(post.board) = 3
    }
}

/**
* 
* Param: 
*/
pred canPlay[r : RoundState] {
    some p: Player | {
        r.turn = p 
        p in r.players
        p.chips > 0 or p.bet = r.highestBet
    }
}

/**
* 
*/
pred playerFolds {
    // Implement logic for player folding
    some p : Player | some r : RoundState | {
        r.players = r.players - p
    }
}

/**
* 
*/
pred playerChecks {
    // Implement logic for player checking
    some p : Player | some s : RoundState | {(p.bet = s.highestBet) {
        p.bet = p.bet
    }}
}

/**
* 
*/
pred playerCalls {
    // Implement logic for player calling
    some p : Player | some s : RoundState | {(p.chips > 0) {
        p.bet = s.highestBet
        p.chips = p.chips - s.highestBet + p.bet
        s.pot = s.pot + s.highestBet - p.bet
    }}
}

/**
* 
*/
pred playerRaises {
    // Implement logic for player raising
    some p : Player | some s : RoundState | some i : Int | {(p.chips > 0) and (i > s.highestBet) {
        p.bet = i
        p.chips = p.chips - i
        s.pot = s.pot + i
        s.highestBet = i
    }}
}

/**
* 
*/
pred playerAllIns {
    // Implement logic for player going all in
    some p : Player | some s : RoundState | {(p.chips > 0) {
        p.bet = p.bet + p.chips
        p.chips = 0
        s.pot = s.pot + p.bet
    }}
}

/**
* 
* Param: 
*/
pred playerAction[r : RoundState] {
    playerChecks or playerCalls or playerRaises or playerAllIns
}

/**
* 
*/
pred traces {
    one preFlop, postRiver: RoundState | {
        winner[postRiver]
        initRound[preFlop]
        all r : RoundState | {
            -- all states are reachable from the initial state
            // r != preFlop implies reachable[r, preFlop, next]
            -- all of the transitions between initial to final state are valid
            some r.next implies validTransition[r, r.next]
        }
    }
    all r : RoundState | {
        winner[r] implies not some r.next
    }
}

/**
* This predicate checks that all cards are unique.
*/
pred uniqueCards {
    all disj c1, c2 : Card | {
        not (c1.rank = c2.rank and c1.suit = c2.suit)
    }
}

/**
* This predicate checks the deck is formed correctly.
*/
pred wellformedDeck {
    uniqueCards
    all c : Card | some r : RoundState {
        c in r.deck
    }
}

/**
* This predicate checks that all players are reachable from each other, meaning there is a cycle of players.
*/
pred playerRotation {
    all p1, p2 : Player | {
        reachable[p1, p2, nextPlayer]
    }
}

/**
* This predicate checks if the player's best hand is a pair.
* Param: p - a player
*/
pred hasPair[p : Player] {
    some r : RoundState | some rank1 : Rank | {
        p.hand = r.board + p.hand
        #{i: Int | (p.hand.cards[i]).rank = rank1} = 2
    }
}

/**
* This predicate checks if the player's best hand is a two pair.
* Param: p - a player
*/
pred hasTwoPair[p : Player] {
    some r : RoundState | some disj rank1, rank2 : Rank | {
        p.hand = r.board + p.hand
        #{i: Int | (p.hand.cards[i]).rank = rank1} = 2 and #{i: Int | (p.hand.cards[i]).rank = rank2} = 2
    }
}

/**
* This predicate checks if the player's best hand is a full house.
* Param: p - a player
*/
pred hasFullHouse[p : Player] {
    hasThreeofaKind[p] and hasPair[p]
}

/**
* This predicate checks if the player's best hand is a straight.
* Param: p - a player
*/
pred hasStraight[p : Player] {
    some r : RoundState | some r1, r2, r3, r4, r5 : Rank | some i1, i2, i3, i4, i5 : Int | {
        p.hand = r.board + p.hand
        (p.hand.cards[i1]).rank = r1 and r2.value = add[r1.value,1]
        (p.hand.cards[i2]).rank = r2 and r3.value = add[r2.value,1]
        (p.hand.cards[i3]).rank = r3 and r4.value = add[r3.value,1]
        (p.hand.cards[i4]).rank = r4 and r5.value = add[r4.value,1]
        (p.hand.cards[i5]).rank = r5
    }
}

/**
* This predicate checks if the player's best hand is a flush.
* Param: p - a player
*/
pred hasFlush[p : Player] {
    some r : RoundState | some suit1 : Suit | {
        p.hand = r.board + p.hand
        #{i: Int | (p.hand.cards[i]).suit = suit1} = 5
    }
}

/**
* This predicate checks if the player's best hand is a royal flush.
* Param: p - a player
*/
pred hasRoyalFlush[p : Player] {
    some r : RoundState | some i1, i2, i3, i4, i5 : Int | {
        hasStraightFlush[p]
        p.hand = r.board + p.hand
        (p.hand.cards[i1]).rank = Ace
        (p.hand.cards[i2]).rank = King
        (p.hand.cards[i3]).rank = Queen
        (p.hand.cards[i4]).rank = Jack
        (p.hand.cards[i5]).rank = Ten
    }
}

/**
* This predicate checks if the player's best hand is a four of a kind.
* Param: p - a player
*/
pred hasFourOfaKind[p : Player] {
    some r: RoundState | some rank1 : Rank | {
        p.hand = r.board + p.hand
        #{i: Int | (p.hand.cards[i]).rank = rank1} = 4
    }
}

/**
* This predicate checks if the player's best hand is a three of a kind.
* Param: p - a player
*/
pred hasThreeofaKind[p : Player] {
    some r: RoundState | some rank1 : Rank | {
        p.hand = r.board + p.hand
        #{i: Int | (p.hand.cards[i]).rank = rank1} = 3
    }
}

/**
* This predicate checks if the player's best hand is a straight flush.
* Param: p - a player
*/
pred hasStraightFlush[p : Player] {
    hasStraight[p] and hasFlush[p]
}

/**
* This predicate checks if the player's best hand is a high card.
* Param: p - a player
*/
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

/**
* This predicate checks the hand a player has and sets the players hand to the type of hand they have.
* Param: p - a player
*/
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

/*
* This predicate maps the possible hands a player can have to a numeric int value to make comparing hands easier.
*/
// inst optimizeHandRank {
//     HighCard = `HighCard
//     `HighCard.score = (-3)
//     Pair = `Pair
//     `Pair.score = (-2)
//     TwoPair = `TwoPair
//     `TwoPair.score = (-1)
//     ThreeOfaKind = `ThreeOfaKind
//     `ThreeOfaKind.score = (0)
//     Straight = `Straight
//     `Straight.score = (1)
//     Flush = `Flush
//     `Flush.score = (2)
//     FullHouse = `FullHouse
//     `FullHouse.score = (3)
//     FourOfaKind = `FourOfaKind
//     `FourOfaKind.score = (4)
// }
// pred handRanks {
//     HighCard.score = -3
//     Pair.score = -2
//     TwoPair.score = -1
//     ThreeOfaKind.score = 0
//     Straight.score = 1
//     Flush.score = 2
//     FullHouse.score = 3
//     FourOfaKind.score = 4
//     StraightFlush.score = 5
//     RoyalFlush.score = 6
// }

/**
* 
*/
pred evaluateHandRun {
    some p : Player | {
        evaluateHand[p]
}
}

run {
    // rankValues
    // optimize_rank
    wellformedDeck
    playerRotation
    // handRanks
    evaluateHandRun
    traces
} for exactly 12 Card, 3 Player, 4 Int for optimize_rank


