# Curiosity-Modeling

1. Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

We are attempting to model a round of Texas Hold'em, a variation of Poker. Our model includes having multiple players be dealt cards, then progressed through multiple different round states (including PreFlop, PostFlop, PostTurn, PostRiver) where the dealer reveals cards for the players by putting the cards on the boards, and all of the players have the opportunity to perform an action, such as raise, call or fold. If after all players have performed an action during the PostRiver state, we then evaluate the hands of the remaining players to determine a winner.

To Note: We are planning on continuing and improving the model as our Final Project. There are currently parts to this model not 100% functional that we plan to fix, and there are aspects of a real game of Texas Hold'em that we are yet to implement. Additionally, we would like to create a custom visualizer as the default visualizer is very messy for this model.

2. Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

We are using the default visualizer as it would have been a massive undertaking to both model Poker and create a custom visualizer for this project. This is something we intend to do when we continue this project as our final project. Our run statement calls wellformedCards, playerRotation, evaluateHandRun, and our traces predicates. You can expect to see an absolute ton of data from an instance produced by the default visualizer, making the table page often more readable than the graph page. On the table page you will see all of our sigs that will be filled with values. By taking a look at the rank and suit sig table you can see all of the cards generated by the instance. Additionally, if you take a look at the deck, board and hands (this is easier to look at on the graph page), you can track where all of the cards are in the game. The final main aspect is the bets and actions of the players, which can be tracked by the highestBet, pot and bet fields. 

We do acknowledge that there are current bugs in our model, mainly regarding the betting actions of the game, as highestBet is sometimes larger than possible, and the bet field does not properly update. 

3. Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

SIGS: Our first sig is RoundState, which contains all of the players, the deck, the board, the pot, the current highest bet, the currentTurn, and the next state. This sig tracks the current state of the round with the highest bet, the board and which players remain, and ensures a valid transition to the next state. The RoundState sig is actually an abstract sig and we have several one time sigs that the RoundState can be one of, these are preFlop, postFlop, postTurn, and postRiver. The next sig is Card, which has fields of rank and suit, which are also sigs. These 3 sigs aim to replicate a regular card from a deck. The last major sig is Player, which has fields of hand (an abstract sig which could be any of the types of poker hands: pair, flush, straight, ... etc), chips (the value of the chips they have remaining), bet (their current bet on the round), and the next player on the board. This sig attempts to emulate a real person sitting at a poker table. 

PREDICATES: 
Our first major predicate is initializing the round. This predicate handles the setup of a round of poker, including the players, the positions (big blind, small blind), the ante's, dealing the initial cards to players. This predicate calls other predicates, such as dealCards, which are all self explanatory. The next major predicate is nextRoundState, this predicate is called when the round is ready to be moved on (all remaining players bets are the same), and it transitions the game into its next state by setting RoundState to its new value and having the dealer perform the appropriate action for the new state. The next 5 predicates are all similar in purpose, but they are the actions a player can take at each point in the round in regards to the bets they choose to play (playerFolds, playerChecks, playerCalls, playerRaises, playerAllIns). Following that there are 10 predicates that determine the type of hand a player has (hasHighCard, hasRoyalFlush, hasStraightFlush, hasFourOfaKind, hasFullHouse, hasFlush, hasStraight, hasThreeofaKind, hasTwoPair, hasPair). The next major predicate is evaluateHand, this predicates determines for each player what is the best type of hand they have using the 10 previously mentioned predicates. The final predicate is findRoundWinner, this predicate awards the round's pot to the winning player based on either that player being the only remaining player or a player having the best hand out of multiple remaining players. 

4. Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

SAMMY TODO:

5. Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.

We have added documentation to every single sig, predicate, and test suite to ensure that our model and test file is well-documented. 