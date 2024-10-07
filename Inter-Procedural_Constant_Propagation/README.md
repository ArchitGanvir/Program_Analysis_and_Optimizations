I made the first submission on 17th April (at 23:59) - the final day before the deadline.
In that submission, I forgot to replace argument variables with their constant values (in at most one store instruction per argument variable), and I have not handled store instructions.

On 18th April (in the afternoon), I made submission 2.
In this submission, I handled the argument variables issue, and I also replaced those store instructions whose pointer argument has only one use (which is the store instruction itself). This also leads to the elimination of additional alloca instructions.
This approach handles most of the store instructions, but does not handle all the store instructions.

On 20th April, I made submission 3 on the "other" branch, wherein I have implemented reaching definitions analysis, which allows us to handle all unnecessary store instructions.

I made another submission on 20th April, in which I have commented the code.

Please consider Submission 2 for evaluation.
