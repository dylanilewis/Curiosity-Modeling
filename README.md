# Curiosity-Modeling

1. Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

We are attempting to model a round of Texas Hold'em, a variation of Poker. Our model includes having multiple players be dealt cards, then progressed through multiple different round states (including PreFlop, PostFlop, PostTurn, PostRiver) where the dealer reveals cards for the players and all of the players have the opportunity to perform an action, such as raise, call or fold. If after all players have performed an action during the PostRiver state, we then evaluate the hands of the remaining players to determine a winner and award the chips in the pot for that round to the winning player.

2. Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

We are using the default visualizer as it would have been a massive undertaking to both model Poker and create a custom visualizer for this project. This is something we intend to do when we continue this project as our final project. Our run statements ... SAMMY TODO You can expect to see SAMMY TODO from an instance produced by the default visualizer. 

3. Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

SIGS: Our first sig is RoundState, which contains all of the players, the deck, the board, the pot, the current highest bet, the buy in for the round, and the value of the ante for the round. This sig has 2 purposes, setting some default values for the round, such as the buy in and the ante, but it also tracks the current state of the round with the highest bet, the board and which players remain. The RoundState sig is actually an abstract sig and we have several one time sigs that the RoundState can be one of, these are preFlop, postFlop, postTurn, and postRiver. The next sig is Card, which has fields of value and suit, which are also sigs. These 3 sigs aim to replicate a regular card from a deck. The last major sig is Player, which has fields of hand (an abstract sig which could be any of the types of poker hands: pair, flush, straight, ... etc), chips (the value of the chips they have remaining), bet (their current bet on the round), and their position on the table (Big Blind, Small Blind or regular). This sig attempts to emulate a real person sitting at a poker table. 

PREDICATES: 
Our first major predicate is initializing the round. This predicate handles the setup of a round of poker, including the players, the positions (big blind, small blind), the ante's, dealing the initial cards to players. This predicate calls other predicates, such as dealCards, which are all self explanatory. The next major predicate is nextRoundState, this predicate is called when the round is ready to be moved on (all remaining players bets are the same), and it transitions the game into its next state by setting RoundState to its new value and having the dealer perform the appropriate action for the new state. The next 5 predicates are all similar in purpose, but they are the actions a player can take at each point in the round in regards to the bets they choose to play (playerFolds, playerChecks, playerCalls, playerRaises, playerAllIns). Following that there are 10 predicates that determine the type of hand a player has (hasHighCard, hasRoyalFlush, hasStraightFlush, hasFourOfaKind, hasFullHouse, hasFlush, hasStraight, hasThreeofaKind, hasTwoPair, hasPair). The next major predicate is evaluateHand, this predicates determines for each player what is the best type of hand they have using the 10 previously mentioned predicates. The final predicate is findRoundWinner, this predicate awards the round's pot to the winning player based on either that player being the only remaining player or a player having the best hand out of multiple remaining players. 

4. Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

SAMMY TODO:

5. Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.

We have added documentation to every single sig, predicate, and test suite to ensure that our model and test file is well-documented. 