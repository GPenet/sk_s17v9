# sk_s17v9
search 17 clues in solution grid with dynamic early end in bands 1+2 expansion

the V6B last version of the search of 17 clues puzzles in a solution grid used a direct expansion of the unavoidable sets found in bands 1+2.
tw switch to a 18 search, the process seemed still too ow. Writing the comments on the process and reading again Gary McGuire's article  on the proof that no 16 clues exists, I realized that I missed in the direct expansion the possibility to go back several steps before the end of the UAs expansion using "higher degree unavoidable sets".
The V9 si in fact the V6 plus a dynamic serach of unavoidable sets requiring 3 or more clues. I decided to make this public n a draft state.

The code starts with a nearly finished implementation of the pass 1 (band 3 ahving 7 clues or more). The pass2 (only 6 clues in band 3) will come later after the test of the pass1.
Some comments on this version can appear in the following discussion
http://forum.enjoysudoku.com/release-of-17-clues-scan-v7b-t42416.html
