#lang forge

open "poker_game.frg"

pred dealCardsTest1{
    all p: Player | some disj c1, c2: Card|{
        c1 in p.hand.cards
        c2 in p.hand.cards
    }
}

pred dealCardsTest2{
    all p: Player | some c1, c2: Card |{
        c1 = c2
        c1 in p.hand.cards
        c2 in p.hand.cards
    }
}

pred dealCardsTest3{
    all p: Player | some c1, c2, c3: Card |{
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in p.hand.cards
    }
}

/**
 * Test suite for the dealCards predicate
 */
test suite for dealCards {
    test expect {
        t1: {dealCardsTest1 and dealCards} is sat
        t2: {dealCardsTest2 and dealCards} is unsat
        t3: {dealCardsTest3 and dealCards} is unsat
    }
}

pred playersChipsGood{
    all p: Player | p.chips = 5
}

pred playersChipsBad{
    one p: Player | p.chips = 3
}

pred playerBadBet{
    one p: Player | p.bet = 3
}

pred playerGoodBet{
    all p: Player | p.bet = 0
}

pred goodRoundState[s: RoundState]{
    s.highestBet = 0
    s.board = none
    s.highestBet = 0
    s.pot = 0
}

pred badRoundState[s: RoundState]{
    s.highestBet = 3
    s.board = none
    s.highestBet = 0
    s.pot = 0
}

/**
 * Test suite for the initRound predicate
 */
test suite for initRound{
    test expect {
        t11: {some r: RoundState | playersChipsGood and goodRoundState[r] and initRound[r]} is sat
        t22: {some r: RoundState | playersChipsBad and goodRoundState[r] and initRound[r]} is unsat
        t33: {some r: RoundState | playersChipsGood and badRoundState[r] and initRound[r]} is unsat
    }
}

pred winnerRoundState1Player[r: RoundState]{
    one p1 :Player | p1 in r.players and #(r.players) = 1
    r = postRiver
}
pred winnerRoundState2Players[r: RoundState]{
    some disj p1, p2 :Player | {
    p1 in r.players 
    p2 in r.players
    #(r.players) = 2
    r = postRiver
    p1.hand.score > p2.hand.score
    }
}

pred badWinnerRoundState[r: RoundState]{
    some disj p1, p2 :Player | {
    p1 in r.players 
    p2 in r.players
    #(r.players) = 2
    r = postRiver
    p1.chips = p1.chips + r.pot
    p2.hand.score > p1.hand.score
    }
}

/**
 * Test suite for the winner predicate
 */
test suite for winner {
    test expect {
        t1winner: {some r: RoundState | winnerRoundState1Player[r] and winner[r]} is sat
        t2winner: {some r: RoundState | winnerRoundState2Players[r] and winner[r]} is sat
        t3winner: {some r: RoundState | badWinnerRoundState[r] and winner[r]} is unsat
    }
}
pred canPlay1[r: RoundState]{
    some p: Player | {
    p in r.players
    p.chips > 0
    r.turn = p
    }

}

pred notHisTurn[r: RoundState]{
    some p: Player | {
    p in r.players
    r.turn != p
}}

pred notInPlayers[r: RoundState]{
    some p: Player | not p in r.players
}

pred notEnoughChips[r: RoundState]{
    some p: Player | {
    p in r.players
    p.chips = 0
}}

/**
 * Test suite for the canPlay predicate
 */
test suite for canPlay {
    test expect {
        t1: {some r: RoundState | canPlay1[r] and canPlay[r]} is sat
        t2: {some r: RoundState | notHisTurn[r] and canPlay[r]} is unsat
        t3: {some r: RoundState | notInPlayers[r] and canPlay[r]} is unsat
        t4: {some r: RoundState | notEnoughChips[r] and canPlay[r]} is unsat
    }
}

pred validTurn1[r: RoundState]{
    some p: Player | {
    p in r.players
    p.bet = r.highestBet
}}

pred notValidTurn1[r: RoundState]{
    some p: Player |{
    p in r.players
    p.bet > r.highestBet
}}

/**
 * Test suite for the validTurn predicate
 */
test suite for validTurn {
    assert canPlay is necessary for validTurn
    test expect {
        t1: {some r: RoundState | canPlay1[r] and validTurn[r]} is sat
        t2: {some r: RoundState | notHisTurn[r] and validTurn[r]} is unsat
        t3: {some r: RoundState | notInPlayers[r] and validTurn[r]} is unsat
        t4: {some r: RoundState | notEnoughChips[r] and validTurn[r]} is unsat
        t5: {some r: RoundState | notValidTurn1[r] and validTurn[r]} is unsat
    }
}

pred preFlopToPostFlop[pre, post: RoundState]{
    some disj c1, c2, c3: Card {
    pre = preFlop
    pre.next = post
    post = postFlop
    pre.board = none
    #(post.board) = 3
}}

pred badPreFlopToPostFlop[pre, post: RoundState]{
    some disj c1, c2, c3: Card {
    pre = preFlop
    pre.next = post
    post = postFlop
    pre.board = none
    #(post.board) = 1
}}

pred postFlopToPostTurn[pre, post: RoundState]{
    pre = postFlop
    pre.next = post
    post = postTurn
    pre.board = post.board
    #(post.board) = 4
}

pred badPostFlopToPostTurn[pre, post: RoundState]{
    pre = postFlop
    pre.next = post
    post = postTurn
    pre.board = post.board
    #(post.board) = 2
}

pred postTurnToPostRiver[pre, post: RoundState]{
    pre = postTurn
    pre.next = post
    post = postRiver
    pre.board = post.board
    #(post.board) = 5
}

pred badPostTurnToPostRiver[pre, post: RoundState]{
    pre = postTurn
    pre.next = post
    post = postRiver
    pre.board = post.board
    #(post.board) = 3
}

/**
 * Test suite for the validTransition predicate
 */
test suite for validTransition {
    assert validTurn is necessary for validTransition
    test expect {
        vt1: {some pre, post: RoundState | preFlopToPostFlop[pre, post] and validTransition[pre, post]} is sat
        vt2: {some pre, post: RoundState | postFlopToPostTurn[pre, post] and validTransition[pre, post]} is sat
        vt3: {some pre, post: RoundState | postTurnToPostRiver[pre, post] and validTransition[pre, post]} is sat
        vt4: {some pre, post: RoundState | badPreFlopToPostFlop[pre, post] and validTransition[pre, post]} is unsat
        vt5: {some pre, post: RoundState | badPostFlopToPostTurn[pre, post] and validTransition[pre, post]} is unsat
        vt6: {some pre, post: RoundState | badPostTurnToPostRiver[pre, post] and validTransition[pre, post]} is unsat
    }
}



pred checkingPlayer {
    some p: Player | some s : RoundState | {
    p in s.players
    p.bet = 3
    s.highestBet = 3
    }
    
}

pred notCheckingPlayer {
    some p: Player | some s : RoundState | {
    p in s.players
    p.bet = 3
    s.highestBet = 4
    }
}

/**
 * Test suite for the playerChecks predicate
 */
test suite for playerChecks {
    test expect {
        t1: {checkingPlayer and playerChecks} is sat
        t2: {notCheckingPlayer and playerChecks} is unsat
    }
}

pred foldingPlayer {
    some p: Player | some s : RoundState | {
        not p in s.players
    }
}

pred notFoldingPlayer {
    some p: Player | some s : RoundState | {
        p in s.players
    }
}

/**
 * Test suite for the playerFolds predicate
 */
test suite for playerFolds {
    test expect {
        t1: {foldingPlayer and playerFolds} is sat
        t2: {notFoldingPlayer and playerFolds} is unsat
    }
}

pred raisingPlayer {
    some p: Player | some s : RoundState | {
    p in s.players
    p.bet > s.highestBet
}}

pred notRaisingPlayer {
    some p: Player | some s : RoundState | {
    p in s.players
    p.bet < s.highestBet
}}

/**
 * Test suite for playerRaises
 */
test suite for playerRaises {
    test expect {
        t1: {raisingPlayer and playerRaises} is sat
        t2: {notRaisingPlayer and playerRaises} is unsat
    }
}

pred callingPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    p.bet = s.highestBet
}

pred notCallingPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    p.bet != s.highestBet
}

/**
 * Test suite for playerCalls
 */
test suite for playerCalls {
    test expect {
        t1: {callingPlayer and playerCalls} is sat
        t2: {notCallingPlayer and playerCalls} is unsat
    }
}
pred allInPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    p.bet = 4
    p.chips = 0
}

pred notAllInPlayer {
    some p: Player | some s : RoundState | 
    p in s.players
    p.bet = 4
    p.chips = 5
}

/**
 * Test suite for playerAllIns
 */
test suite for playerAllIns{
    test expect {
        t1: {allInPlayer and playerAllIns} is sat
        t2: {notAllInPlayer and playerAllIns} is unsat
    }
}

/**
 * Test suite for playerAction predicate
 */
test suite for playerAction{
    assert playerFolds is sufficient for playerAction
    assert playerChecks is sufficient for playerAction
    assert playerRaises is sufficient for playerAction
    assert playerCalls is sufficient for playerAction
    assert playerAllIns is sufficient for playerAction
}

/**
 * Test suite for the traces predicate
 */
test suite for traces{
}

pred sameCardInDeck{
    some c1, c2: Card | some r: RoundState | {
        c1 = c2
        c1 in r.deck
        c2 in r.deck
}}

pred cardInBoardAndDeck{
    some c: Card | some r: RoundState | {
        c in r.board
        c in r.deck
}}

pred cardInHandAndDeck{
    some c: Card | some p: Player | some r: RoundState | {
        c in p.hand.cards
        c in r.deck
}}

pred cardInHandAndBoard{
    some c: Card | some p: Player | some r: RoundState | {
        c in p.hand.cards
        c in r.board
}}

pred wellformedCards1{
    all r: RoundState | some c: Card | {
        c in r.deck => not c in r.board => {
            some p: Player | {not c in p.hand.cards}
        }
    }
}

/**
 * Test suite for wellformedCards predicate
 */
test suite for wellformedCards{
    test expect {
        wellformedt1: {sameCardInDeck and wellformedCards} is unsat
        wellformedt2: {cardInBoardAndDeck and wellformedCards} is unsat
        wellformedt3: {cardInHandAndDeck and wellformedCards} is unsat
        wellformedt4: {cardInHandAndBoard and wellformedCards} is unsat
        wellformedt5: {wellformedCards1 and wellformedCards} is sat
    }
}

pred playerRotation1{
    some disj p1, p2: Player | some r: RoundState | {
        p1 in r.players
        p2 in r.players
        p1 = r.turn
        p2 = r.turn.next
    }
}

pred badPlayerRotation1{
    some disj p1, p2, p3: Player | some r: RoundState | {
        p1 in r.players
        p2 in r.players
        p3 in r.players
        p1 = r.turn
        p2 = r.turn.next
    }
}

/**
 * Test suite for playerRotation predicate
 */
test suite for playerRotation{
    test expect {
        t1: {playerRotation1 and playerRotation} is sat
        t2: {badPlayerRotation1 and playerRotation} is unsat
    }
}

pred playerHasPair1[p: Player]{
    some r: RoundState | some disj c1, c2: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c1.rank = c2.rank
    }
}

pred playerHasPair2[p: Player]{
    some r: RoundState | some disj c1, c2: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c1.rank = c2.rank
    }
}

pred playerHasNoPair[p: Player]{
    some r: RoundState | some disj c1, c2: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c1.rank != c2.rank
    }
}

/**
 * Test suite for hasPair
 */
test suite for hasPair{
    test expect {
        pairTest1: {some p: Player | playerHasPair1[p] and hasPair[p]} is sat
        pairTest3: {some p: Player | playerHasPair2[p] and hasPair[p]} is sat
        pairTest2: {some p: Player | playerHasNoPair[p] and hasPair[p]} is unsat
    }
}

pred playerHasTwoPair1[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in r.board
        c4 in r.board
        c1.rank = c2.rank
        c3.rank = c4.rank
    }
}

pred playerHasTwoPair2[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c1.rank = c2.rank
        c3.rank = c4.rank
    }
}
pred notPlayerHasTwoPair[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in r.board
        c4 in r.board
        c1.rank != c2.rank
        c3.rank != c4.rank
    }
}

/**
 * Test suite for hasTwoPair
 */
test suite for hasTwoPair{
    test expect {
        twoPairTest1: {some p: Player | playerHasTwoPair1[p] and hasTwoPair[p]} is sat
        twoPairTest2: {some p: Player | playerHasTwoPair2[p] and hasTwoPair[p]} is sat
        twoPairTest3: {some p: Player | notPlayerHasTwoPair[p] and hasTwoPair[p]} is unsat
    }
}

pred playerHasThreeOfAKind1[p: Player]{
    some r: RoundState | some disj c1, c2, c3: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c1.rank = c2.rank
        c2.rank = c3.rank
    }
}

pred playerHasThreeOfAKind2[p: Player]{
    some r: RoundState | some disj c1, c2, c3: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in r.board
        c1.rank = c2.rank
        c2.rank = c3.rank
    }
}

pred notPlayerHasThreeOfAKind[p: Player]{
    some r: RoundState | some disj c1, c2, c3: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c1.rank != c2.rank
        c2.rank != c3.rank
    }
}

/**
 * Test suite for hasThreeOfAKind
 */
test suite for hasThreeOfAKind{
    test expect {
        threeOfAKindTest1: {some p: Player | playerHasThreeOfAKind1[p] and hasThreeOfAKind[p]} is sat
        threeOfAKindTest2: {some p: Player | playerHasThreeOfAKind2[p] and hasThreeOfAKind[p]} is sat
        threeOfAKindTest3: {some p: Player | notPlayerHasThreeOfAKind[p] and hasThreeOfAKind[p]} is unsat
    }
}

pred playerHasFourOfAKind[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c1.rank = c2.rank
        c2.rank = c3.rank
        c3.rank = c4.rank
    }
}

pred notPlayerHasFourOfAKind[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c1.rank != c2.rank
        c2.rank != c3.rank
        c3.rank != c4.rank
    }
}

/**
 * Test suite for hasFourOfAKind
 */
test suite for hasFourOfAKind{
    test expect {
        fourOfAKindTest1: {some p: Player | playerHasFourOfAKind[p] and hasFourOfAKind[p]} is sat
        fourOfAKindTest2: {some p: Player | notPlayerHasFourOfAKind[p] and hasFourOfAKind[p]} is unsat
    }
}

pred playerHasFullHouse1[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank = c2.rank
        c3.rank = c4.rank
        c4.rank = c5.rank
    }
}

pred notPlayerHasFullHouse[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank != c2.rank
        c3.rank != c4.rank
        c4.rank != c5.rank
    }
}

/**
 * Test suite for hasFullHouse
 */
test suite for hasFullHouse{
    assert hasThreeOfAKind is necessary for hasFullHouse
    assert hasPair is necessary for hasFullHouse
    test expect {
        fullHouseTest1: {some p: Player | playerHasFullHouse1[p] and hasFullHouse[p]} is sat
        fullHouseTest2: {some p: Player | notPlayerHasFullHouse[p] and hasFullHouse[p]} is unsat
    }
}

//Straight

pred playerHasStraight1[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank = add[c2.rank, 1]
        c2.rank = add[c3.rank + 1]
        c3.rank = add[c4.rank + 1]
        c4.rank = add[c5.rank + 1]
    }
}

pred playerHasStraight2[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank = subtract[c2.rank, 1]
        c2.rank = subtract[c3.rank, 1]
        c3.rank = subtract[c4.rank, 1]
        c4.rank = subtract[c5.rank, 1]
    }
}

pred notPlayerHasStraight1[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank.value = -3
        c2.rank.value = -1
        c3.rank.value = 1
        c4.rank.value = 1
    }
}

pred notplayerHasStraight2[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank.value = -3
        c2.rank.value = -3
        c3.rank.value = 2
        c4.rank.value = 2
    }
}

/**
 * Test suite for hasStraight
 */
test suite for hasStraight{
    test expect {
        straightTest1: {some p: Player | playerHasStraight1[p] and hasStraight[p]} is sat
        straightTest2: {some p: Player | playerHasStraight2[p] and hasStraight[p]} is sat
        straightTest3: {some p: Player | notPlayerHasStraight1[p] and hasStraight[p]} is unsat
        straightTest4: {some p: Player | notplayerHasStraight2[p] and hasStraight[p]} is unsat
    }
}

//Flush
pred playerHasFlush1[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.suit = c2.suit
        c2.suit = c3.suit
        c3.suit = c4.suit
        c4.suit = c5.suit
    }
}

pred notPlayerHasFlush1[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.suit = c2.suit
        c2.suit = c3.suit
        c3.suit = c4.suit
        c4.suit != c5.suit
    }
}

/**
 * Test suite for hasFlush
 */
test suite for hasFlush{
    test expect {
        flushTest1: {some p: Player | playerHasFlush1[p] and hasFlush[p]} is sat
        flushTest2: {some p: Player | notPlayerHasFlush1[p] and hasFlush[p]} is unsat
    }
}

//Straight Flush
/**
 * Test suite for hasStraightFlush
 */
test suite for hasStraightFlush{
    assert hasStraight is necessary for hasStraightFlush
    assert hasFlush is necessary for hasStraightFlush
    test expect {
        straightFlushTest1: {some p: Player | playerHasFlush1[p] and playerHasStraight1[p] and hasStraightFlush[p]} is sat
        straightFlushTest2: {some p: Player | notPlayerHasFlush1[p] and notPlayerHasStraight1[p] and hasStraightFlush[p]} is unsat
    }
}

//Royal Flush

pred playerHasRoyalFlush[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in p.hand.cards
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank = Ace
        c2.rank = King
        c3.rank = Queen
        c4.rank = Jack
        c5.rank = Ten
        c1.suit = c2.suit
        c2.suit = c3.suit
        c3.suit = c4.suit
        c4.suit = c5.suit
    }
}

pred notPlayerHasRoyalFlush[p: Player]{
    some r: RoundState | some disj c1, c2, c3, c4, c5: Card | {
        p in r.players
        c1 in p.hand.cards
        c2 in r.board
        c3 in r.board
        c4 in r.board
        c5 in r.board
        c1.rank = Ace
        c2.rank = Three
        c3.rank = Queen
        c4.rank = Five
        c5.rank = Ten
        c1.suit = c2.suit
        c2.suit != c3.suit
        c3.suit = c4.suit
        c4.suit != c5.suit
    }
}

/**
 * Test suite for hasRoyalFlush
 */
test suite for hasRoyalFlush{
    assert hasStraightFlush is necessary for hasRoyalFlush
    test expect {
        royalFlushTest1: {some p: Player | playerHasRoyalFlush[p] and hasRoyalFlush[p]} is sat
        royalFlushTest2: {some p: Player | notPlayerHasFlush1[p] and notPlayerHasStraight1[p] and hasRoyalFlush[p]} is unsat
        royalFlushTest3: {some p: Player | notPlayerHasRoyalFlush[p] and hasRoyalFlush[p]} is unsat
    }
}

//High Card
pred hasHighCard1[p: Player]{
    not hasPair[p]
    not hasTwoPair[p]
    not hasThreeOfAKind[p]
    not hasStraight[p]
    not hasFlush[p]
    not hasFullHouse[p]
    not hasFourOfAKind[p]
    not hasStraightFlush[p]
    not hasRoyalFlush[p]
}

/**
 * Test suite for hasHighCard
 */
test suite for hasHighCard{
    test expect {
        highCardTest1: {some p : Player | hasHighCard1[p] and hasHighCard[p]} is sat
        highCardTest2: {some p : Player | hasPair[p] and hasHighCard[p]} is unsat
        highCardTest3: {some p : Player | hasTwoPair[p] and hasHighCard[p]} is unsat
        highCardTest4: {some p : Player | hasThreeOfAKind[p] and hasHighCard[p]} is unsat
        highCardTest5: {some p : Player | hasStraight[p] and hasHighCard[p]} is unsat
        highCardTest6: {some p : Player | hasFlush[p] and hasHighCard[p]} is unsat
        highCardTest7: {some p : Player | hasFullHouse[p] and hasHighCard[p]} is unsat
        highCardTest8: {some p : Player | hasFourOfAKind[p] and hasHighCard[p]} is unsat
        highCardTest9: {some p : Player | hasStraightFlush[p] and hasHighCard[p]} is unsat
        highCardTest10: {some p : Player | hasRoyalFlush[p] and hasHighCard[p]} is unsat
    }
}

//EvaluateHands
pred correctEvaluateHands1{
    some r: RoundState | some p: Player | {
        p in r.players
        p.hand.score = -4
        hasHighCard[p]
    }
}   

pred correctEvaluateHands2{
    some r: RoundState | some p: Player | {
        p in r.players
        p.hand.score = -3
        hasPair[p]
    }
}

pred correctEvaluateHands3{
    some r: RoundState | some p: Player | {
        p in r.players
        p.hand.score = -2
        hasTwoPair[p]
    }
}

pred incorrectEvaluateHands1{
    some r: RoundState | some p: Player | {
        p in r.players
        p.hand.score = 0
        hasPair[p]
    }
}

pred incorrectEvaluateHands2{
    some r: RoundState | some p: Player | {
        p in r.players
        p.hand.score = 1
        hasTwoPair[p]
    }
}

pred incorrectEvaluateHands3{
    some r: RoundState | some p: Player | {
        p in r.players
        p.hand.score = 2
        hasRoyalFlush[p]
    }
}

/**
 * Test suite for evaluateHands
 */
test suite for evaluateHands{
    test expect {
        evaluateHandsTest1: {correctEvaluateHands1 and evaluateHands} is sat
        evaluateHandsTest2: {correctEvaluateHands2 and evaluateHands} is sat
        evaluateHandsTest3: {correctEvaluateHands3 and evaluateHands} is sat
        evaluateHandsTest4: {incorrectEvaluateHands1 and evaluateHands} is unsat
        evaluateHandsTest5: {incorrectEvaluateHands2 and evaluateHands} is unsat
        evaluateHandsTest6: {incorrectEvaluateHands3 and evaluateHands} is unsat
    }
}