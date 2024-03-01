#lang forge

abstract sig RoundState {
    players: set Player,
    deck: set Card,
    board: set Card,
    pot: one Int,
    highestBet: one Int,
    turn: one Player,
    next: lone RoundState
}   

one sig preFlop, postFlop, postTurn, postRiver extends RoundState {}

sig Card {
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
    hand: one Hand,
    chips: one Int,
    bet: one Int,
    nextPlayer: one Player
}

sig Hand {
    // the hand of a player
    cards: set Card,
    score: one Int
}

// one sig RoyalFlush, StraightFlush, FourOfaKind, FullHouse, Flush, Straight, ThreeOfaKind, TwoPair, Pair, HighCard extends Hand {}

/**
* This predicate maps the rank of cards to numeric values to make comparing cards easier 
*/

/**
* This predicate checks that all cards are unique.
*/
pred uniqueCards {
    all disj c1, c2 : Card | {
        not (c1.rank = c2.rank and c1.suit = c2.suit)
    }
}


/**
* This predicate ensures that all players are dealt 2 cards.
*/
pred dealCards {
    all disj p1, p2 : Player | some disj card1, card2: Card | {
        // p1 != p2
        #(p1.hand.cards) = 2
        // #{i: Int | (p.hand.cards[i]) = card1} = 1
        // #{i: Int | (p.hand.cards[i]) = card2} = 1
        p1.hand.cards != p2.hand.cards
        p1.hand.cards = card1 + card2
}
}

/**
* This predicate implements the logic of initializing a round of poker. It ensures the board is empty,
* the players are dealt cards, the players have the correct amount of chips, and the turn is set to the first player.
* Param: r - a round state
*/
pred initRound[r : RoundState] {
    r = preFlop
    r.board = none
    r.highestBet = 0
    r.pot = 0
    dealCards
    all p : Player | {
        p.bet = 0
        p.chips = 5
        p.hand = none
    }
    one p : Player | {
        p = r.turn
    }
}

/**
* This predicate implements the needed constraints for a winner to be named. A player must either be the 
* last remaining player or have the best hand at the end of the round.
* Param: r - a round state
*/
pred winner[r : RoundState] {
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
* This predicate checks that a turn is valid. If a player can play, they must play. If they cannot play, they must fold.
* After a move is made the turn is updated to the next player.
* Param: r - a round state
*/
pred validTurn[r : RoundState] {
    canPlay[r] implies playerAction[r] else playerFolds
    r.turn = r.turn.nextPlayer
}

/**
* This predicate checks that a transition is valid. All players must have made a valid move and then the
* round state is updated to the next round state depending on the pre round state.
* Param: pre - the current round state
* Param: post - the next round state
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
        #(pre.board) = 3
        #(post.board) = 4
    }
    pre = postTurn implies {
        post = postRiver
        #(pre.board) = 4
        #(post.board) = 5
    }
}

/**
* This predicate implements the constraints for a player to be able to play. It must be a players turn, 
* the player must still be in the game, and a player must either have more than 0 chips or their current bet must
* be equal to the highest bet.
* Param: r - a round state
*/
pred canPlay[r : RoundState] {
    some p: Player | {
        r.turn = p 
        p in r.players
        p.chips > 0 or p.bet = r.highestBet
    }
}

/**
* This predicate implements the logic of a player folding. The player is removed from the round state and will remain
* removed until the round is over.
*/
pred playerFolds {
    some p : Player | some r : RoundState | {
        r.players = r.players - p
    }
}

/**
* This predicate implements the logic of a player checking. Their current bet must be equal to the highest bet, and
* the players bet remains the same.
*/
pred playerChecks {
    some p : Player | some s : RoundState | {(p.bet = s.highestBet) {
        p.bet = p.bet
    }}
}

/**
* This predicate implements the logic of a player calling. The player must have more than 0 chips, and their bet is set
* to the highest bet. The players chips are updated and the pot is updated.
*/
pred playerCalls {
    some p : Player | some s : RoundState | {(p.chips > 0) and (subtract[s.highestBet, p.bet] <= p.chips) {
        p.bet = s.highestBet
        p.chips = add[subtract[p.chips, s.highestBet], p.bet]
        s.pot = subtract[add[s.pot, s.highestBet], p.bet]
    }}
}

/**
* This predicate implements the logic of a player raising. The player must have more than 0 chips, and their new bet must be 
* greater than the highest bet. The players chips are updated, the pot is updated, and the highest bet is updated.
*/
pred playerRaises {
    some p : Player | some s : RoundState | some i : Int | {(p.chips > 0) and (i > s.highestBet) and (i <= p.chips) {
        p.bet = i
        p.chips = subtract[p.chips, i]
        s.pot = add[s.pot, i]
        s.highestBet = i
    }}
}

/**
* This predicate implements the logic of a player going all in. The player must have more than 0 chips, and their bet is set
* to their remaining chips. The players remaining chips are set to 0 and the pot is updated.
*/
pred playerAllIns {
    some p : Player | some s : RoundState | {(p.chips > 0) {
        p.bet = add[p.bet, p.chips]
        p.chips = 0
        s.pot = add[s.pot, p.bet]
    }}
}

/**
* This predicate checks if the player has a valid action to take. Calling 4 of the above player action predicates. 
* Param: r - a round state
*/
pred playerAction[r : RoundState] {
    playerChecks or playerCalls or playerRaises or playerAllIns
}

/**
* This predicate handles the logic of the overall game. It first initializes the game in its preflop state, it then checks
* that there is a winner in its final postRiver state. Then for all states in the game, it checks that there is a valid
* transition to the next state. Finally, it checks that once there is a winner the game stops and there are no new states. 
*/
pred traces {
    one preFlop, postRiver: RoundState | {
        initRound[preFlop]
        winner[postRiver]
        all r : RoundState | {
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
* This predicate checks the deck, board and all player's hands are formed correctly.
*/
pred wellformedCards {
    uniqueCards
    all c : Card | all r : RoundState | {
        c in r.deck implies {
            c not in r.board
            all p : Player | {
                c not in p.hand
            }
        }
        c in r.board implies {
            c not in r.deck
            all p : Player | {
                c not in p.hand
            }
        }
        some disj p1, p2 : Player {
            c in p1.hand implies {
                c not in r.deck
                c not in r.board
                c not in p2.hand
            }
        }
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
        #{i : Int | (p.hand.cards[i]).rank = rank1} = 2 and #{i : Int | (p.hand.cards[i]).rank = rank2} = 2
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
    hasRoyalFlush[p] implies p.hand.score = 5
    hasStraightFlush[p] implies p.hand.score = 4
    hasFourOfaKind[p] implies p.hand.score = 3
    hasFullHouse[p] implies p.hand.score = 2
    hasFlush[p] implies p.hand.score = 1
    hasStraight[p] implies p.hand.score = 0
    hasThreeofaKind[p] implies p.hand.score = -1
    hasTwoPair[p] implies p.hand.score = -2
    hasPair[p] implies p.hand.score = -3
    hasHighCard[p] implies p.hand.score = -4
}

/**
* 
*/
pred evaluateHandRun {
    some p : Player | {
        evaluateHand[p]
}
}

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

    
}

run {
    wellformedCards
    playerRotation
    // evaluateHandRun
    traces
} for exactly 12 Card, 2 Player, 4 Int for optimize_rank


