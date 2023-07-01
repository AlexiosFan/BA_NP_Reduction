## More general remarks:

- when you cite, eg Cook~[Coo23], make sure to have a blank before the citation but no line break. Latex: Cook~\cite{cook}
- Capitalization of Section headings



## Remarks Introduction

- 1.1 First paragraph: What is your main statement? Do you want to give examples to real-life NP-hrad problems? Then Go and Chess are not good examples, because they are in P (only finite number of states). Maybe find better examples for NP-hard real-life problems. If you just make examples for decision problems, then make clear what the decision is. Eg: in chess: what is the best winning move I can make right now? / Does there exist a winning strategy? / Can I do checkmate in n steps?
- Maybe last sentence of first paragraph as introductory sentence in second paragraph?
- First sentence of second paragraph not straight. Verbs are strange.
- Example NP-hard problems
- What is the complexity class P? You did not define it yet.
- Is sounds like there are algorithms that can efficiently compute NP-hard problems. Reformulate: Only approximations/heuristics for NP-hard problems are efficiently implementable.
- What is efficient? (= poly-time)
- Separate paragraph for reductions: What is the aim, (maybe examples), what is a poly-time reduction? (Then the connection with your next paragraph is better)
- Why do you need automatic verification? (= humans make errors, computers less)
- cite Karp21 project's web page!
- 1.2 All Problem names capitalized (check throughout whole document)
- Set coverings sentence: I don't get it
- s.t. = such that, no shortening in text! (only in math formulas)
- Application of your work?
- 1.3: Merge paragraphs about chapter 3+4, adapt if examples are in main body

## Remarks Preliminaries

- cite afp





## Remarks Set Covering Problems

- I like that you give a first introductory paragraph before starting with section 3.1. Can you do that with the other sections as well? done 
- in intro after 3. : after i.e. there is too much space. This is a Latex problem, since it interprets the full stop after i.e. (or eg.) as a full full stop. You should use "i.e.\ " with a backslash directly behind the full stop to get a shorter white space. done 
- Citation of Karp's paper is missing done 
- 3.1: consistently use either blabla problem or just blabla (usually blabla problem makes more sense as an English sentence) **pending**
- "In Exact Cover, it no only..." what is "it"? What is the topic of that sentence? Better: The Exact Cover problems not only asks... but also ... done 
- Def 6 here s.t. is ok to abbreviate, but we have the full stop problem again. done 
- What you define as the "Exact Cover" set is actually just the set of YES-instances. You need to make this distinction clear! (emphasize in preliminaries)
- Are we missing the disjoint part of Def 6 in the Exact Cover set? done 
- "... many different reductions available." Available is a strange word to use here. Maybe ...can be found in the literature. (answer to: where available?)
- Discussion about different approaches very interesting. Good! 
- 3.1.2 State once again that you are reducing  from SAT, after the discussion the reader might be confused. State that you now define the reduction function
- Here, highlighting does make sense, maybe use a lighter gray to have better contrast
- Did you define what fuction vars is? Better: When you introduce SAT in Preliminaries, explain about the type and how you model is (list/set of sets of literals) and introduce notation that you might need. This is better for the later understanding than the code snippets you currently have. **pending**
- Numbers in a text lower than 10 are usually written as a word, eg here three different kinds of objects (for S, you spelled four out :) done 
- Define X and S dependent on F! X and S are functions taking F as input, eg X(F) **doubt**
- Transitional sentence: After defining the reduction function, we now state the lemma ... **done**
- Lemma 1: "Let F be satisfiable": what is F? a clause, a SAT instance, a formula, a variable? 
- Write X and S as dependent on the input F! (everywhere!)
- Proof: Did you define what a "valid assignment" is? Did you define the symbols top and bottom?  What does this stand for? **pending**
- Proof: How can you conclude that clauses and variables are covered from knowing S' is disjoint? 
- I can't follow the last paragraph of proof Lemma 1. Please rewrite and make the logical implications clear. **pending**
- Transitional sentence between Lemma 1 end proof and Lemma 2 & before Lemma 3
- Proof of Lemma 2: Give more details! How do you reconstruct the model? (Never write: it is easy to... if it is that easy, just give a short explanation)
- Lemma 3: polynomial -> can be computed in polynomial **time**
- "indicating a linear complexity" => for the computation of X
- "Apparently" feels strange, better: Then (logical connector)
- "Thus, the construction " => of S
- Your central claim is missing at the end! Theorem: Exact Cover is NP-hard. Proof Lemma 1+2+3!
- 3.1.3: primary is a strange word here, maybe: A definition along the lines of \eqref (ExCo)...
- To discuss the choice of definitions is nice.
- "A Container Type" : can you leave out the A? That looks weird in comparison to all your other captions. Or maybe "Container Type for the Construction of S"
- What you call a container type: is this the "data type" from Isabelle? Then you should call it data type, not container type. (Please check the semantics book by Tobias Nipkow for the correct term)
- "Intuitively, ... clause[s]"
- s.t. => such that (check everywhere)
- Why do you need to include the clause in the literal for defining L?
- do you reference and explain Figures 3.4 and 3.5? Why do you include them? What information should the reader get from them?
- "less interesting" => follows the mathematical proof very precisely/ something else?. Find another expression, so that you don't state that your work is "less interesting". Even if it might have been a bit boring, it is still an important result (and impressive work) that you managed to get through all the fiddly bits of the proof. 
- Polynomial-time Complexity: "are need[ed]" "metric[]\footnote"
- footnote: previous results: cite them!    It was also correct => Since these reductions only depended on..., this issue was not addressed/experienced.
- Rest of 3.1.3: Rework code snippets/ table?


# Working tree


## Remarks Set Covering Problems

- 3.1: consistently use either blabla problem or just blabla (usually blabla problem makes more sense as an English sentence) **pending**

- Did you define what fuction vars is? Better: When you introduce SAT in Preliminaries, explain about the type and how you model is (list/set of sets of literals) and introduce notation that you might need. This is better for the later understanding than the code snippets you currently have. **pending**

- Define X and S dependent on F! X and S are functions taking F as input, eg X(F) **doubt**
- Write X and S as dependent on the input F! (everywhere!)

- Proof: Did you define what a "valid assignment" is? Did you define the symbols top and bottom?  What does this stand for? **pending**
 







