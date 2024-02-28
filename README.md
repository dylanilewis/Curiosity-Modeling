# Curiosity-Modeling

1. Project Objective: What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.

We are attempting to model a round of Texas Hold'em, a variation of Poker. Our model includes having multiple players be dealt cards, then progressed through multiple different round states (including PreFlop, PostFlop, PostTurn, PostRiver) where the dealer reveals cards for the players and all of the players have the opportunity to perform an action, such as raise, call or fold. If after all players have performed an action during the PostRiver state, we then evaluate the hands of the remaining players to determine a winner and award the chips in the pot for that round to the winning player.

2. Model Design and Visualization: Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

We are using the default visualizer as it would have been a massive undertaking to both model Poker and create a custom visualizer for this project. This is something we intend to do when we continue this project as our final project. Our run statements ... You can expect to see ... from an instance produced by the default visualizer. 

3. Signatures and Predicates: At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

Our first sig is RoundState, which contains all of the players, the deck, the board, the pot, the current highest bet, the buy in for the round, and the value of the ante for the round. This sig has 2 purposes, setting some default values for the round, such as the buy in and the ante, but it also tracks the current state of the round with the highest bet, the board and which players remain. The RoundState sig is actually an abstract sig and we have several one time sigs that the RoundState can be one of, these are preFlop, postFlop, postTurn, and postRiver. 

4. Testing: What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

Answer here.

5. Documentation: Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.

We have added documentation to every single sig, predicate, and test suite to ensure that our model and test file is well-documented. 