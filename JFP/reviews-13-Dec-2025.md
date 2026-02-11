> Although this work may potentially be published in Journal of
> Functional Programming, the reviewers have suggested some major
> revisions to your manuscript.  Therefore, I invite you to respond to
> the reviewers' comments and revise your manuscript.  Two out of three
> reviewers are fairly happy with the manuscript; the third less so.  As
> they point out "Richard Bird's advice for pearl reviews suggests
> stopping when 'too much specialist knowledge is needed' -- and I felt
> dangerously close to stopping in this section."  Do you really need to
> rely on parametricity? (My understanding is that you cannot prove
> parametricity within Agda but that a suitable rule can be added to the
> type theory without compromising soundness.)

[TODO]

* Quote Referee 1’s summary (‘instead of a complex calculation-style proof’) and Referee 3’s comment on L332
* Other proofs are of course possible, but our goal is this particular parametricity-based proof.

> Perhaps you should try
> to identify a (a single) message that you want to get across: (a) the
> use of dependent types to capture structure that is implicit in the
> original work; (b) the use of parametricity to show the equivalence of
> two recursion schemes. For (a): polish the definitions; natural
> numbers seem to be over-used.

[TODO]

* (Drop defined only for immediate sublists, and then use reflexive transitive closure) but this complicates the definition (and doesn’t match BT)
* Natural termination measure for the bottom-up algorithm
* Input type of retabulate

> For (b): this requires a more careful
> introduction possibly using a simpler example.

[FIXME]

* Induction principle on natural numbers

> Finally, try to avoid
> jargon (relative monad; codensity representation); instead, explain
> the concepts and their purpose.

[FIXME]

* Expand the monad definitions

> Reviewers' Comments to Author:
> Referee: 1
>
> Comments to the Author
>
> This paper revisits the problem of how to write an efficient
> programmed definition of a function over lists that recursively
> depends on results for all immediate sublists, and how to prove that
> the efficient definition is equivalent to the obvious but inefficient
> specification. The authors show how this can be done in a dependently
> typed setting, using parametricity instead of a complex
> calculation-style proof.
>
> At times the paper becomes quite technical. In places a little more
> explanation would help.  There are a few phrasing issues. However,
> with minor revisions I think it would make a suitable JFP Pearl.
>
> I shall first list a few issues I'd like to see addressed, and then
> make a few suggestions for phrase-level changes.
>
> Issues to be addressed:
> 1. In the Introduction please give some motivating examples of specific functions that have list
> arguments and are specified by recursion over all immediate sublists.

We were motivated by the puzzling definition of upgrade (which, at least to Referee 3 as well, is a sufficient motivation), so specific problems have never been our motivation.  That being said, we’ve added Footnote 1 to mention a few kinds of problem (including a reference to a paragraph in Mu’s [2024] paper), but we avoid providing specific detail and distracting the reader.

> 2. You say on p2 "It may appear that this bottom-up strategy can be implemented
> by representing each level as a list, but this turns out to be impossible."
> Please briefly explain why, also making clear what you mean by "impossible".

There was an explanation in our previous paper [Ko et al. 2025, Section 1.2], but it was somewhat involved (and the reviewers didn’t appreciate it).  We think it’s better to omit the remark than include the explanation, or the reader will likely get stuck here.

> 3. You say on p2 that the definition of upgrade "is not valid Agda".
> Please explain why not, as you do on p5 for the specification (1.1) where the problem is the
> termination check.

The explanation is not a one-liner and would be too much to include in the main text, so we merge it with other information about upgrade into Footnote 3.

> 4. On p4 you first say that "result type M should be a monoid", but then go on to say "monoid
> laws ... are not needed in our development".
> This seems a little confusing. I'm guessing that you find it convenient for M to satisfy the
> Monoid signature, though in algebraic terms M need not actually be a monoid. OK, but since M
> is used in the "codensity representation" of a "(relative) monad" --- you may be stretching the
> reader here! --- does this mean it need not actually be a monad either? Perhaps you could make
> the explanation clearer and simpler.

[FIXME]

* Expand on the codensity representation

> 5. On p5 you say "We will prove that the two algorithms are extensionally equal in Section 5, to
> understand which it will not be necessary to know how the two algorithms are implemented".
>
> Understanding is subjective. Could you say instead that the proof will not depend on
> implementation details of the two algorithms, but only on their shared dependent type?

We’ve put your sentence into the paper — thanks!

> 6. On p6, at the start of Section 4, you say "Given an input list xs, the bottom-up algorithm bu
> first creates a tree representing 'level -1' below the lattice in Fig. 2. This 'basement' level
> contains results for those sublists obtained by removing suc (length xs) elements from xs; there
> are no such sublists, so the tree contains no elements, although the tree itself still exists
> (representing a proof of a vacuous universal quantification)".
> This appeal to an imaginary level below the lattice seems very contrived. Since there are no lists
> shorter than the empty list, it's not surprising that "the tree contains no elements", but it is
> surprising that it cannot be expressed as a "nil" tree. All the more so as you say on the previous
> page "We will see in Section 4 why it is beneficial to include nil." Please explain why nil is no
> good here.

[TODO]

* Basement level as the starting point going up the levels
* Explain in the response but not in the paper to avoid distraction

> 7. On p7 you say "just follow the types, and most of the program writes itself. It is not
> particularly important to understand the program --- in fact, any program works as long as it is
> type-correct".
> This situation only comes about because of the sophistication of the type system. There are three
> balancing observations you might consider: (1) devising correct types requires more
> sophistication from the programmer, (2) sometimes, as with the base example, an expression of
> the right type is more complicated that one might expect, and (3) it is generally preferable for
> programmers to understand programs they have written!

[FIXME]

* Depends on the level of abstraction we (currently) want to be: overall structure -> the type sufficees; program detail -> the types help to write and understand the program
* The paper wants to focus on the overall structure.

> 8. Also on p7 you say "We avoid those somewhat tedious conditions by including nil in Drop to
> represent the empty levels, and in exhange need to deal with these levels, which are easy to deal
> with though."
> In view of issues 6 & 7 you might omit the last seven words!

We change ‘easy’ to ‘easier’ since this paragraph intends to compare our solution with Mu’s.

> 9. In the abstract, and again on p10, you say that your development in this paper is "more
> economical" than the previous equational derivation. Please explain what you mean here. Is it,
> for example, that the proof developed is shorter and simpler? Or that it involves less work, or
> less difficult work, for the developer --- perhaps because more work is done by the
> implementation of the dependent-type machinery? Or something else again?

[TODO]

* The purpose of the entire S6.2 is to answer this question (in particular there’s a sentence ‘the proof of bu’s parametricity would essentially be the proof of equation (5) generalised to all invariants’)

> Rephrasing suggestions:
>
> KEY: / / insert, [ ] delete, [ -> ] replace
> p1 "the former" and "the latter" are notoriously awkward for readers. The last clause of the
> abstract could more simply be "our proof can be understood as a more economical version of
> Mu's equational proof".

Changed ‘the latter’ to ‘Mu's proof’.

> p2 "[which is directly] translated"

Changed to a sentence in Footnote 3.

> p3 "will [just] give a more general definition of /all/ sublists"

Deleted.

> p4 "If [this implies that] P holds"

We’re saying what the type of f below says.

> p5 "Note that ... [that has -> with] an additional"

Changed.

> p5 "In [the subsequent] Sections 3 and 4"

Deleted.

> p7 "similar [version of the] exercise"

Deleted.

> p11 "enough information [for stating that -> to guarantee a similar invariant]"

We do mean that there’s not enough information for writing down the invariant. ‘Guarantee a similar invariant’ looks more vague.

> p12 (in Mu ref.) "[e]14:1-16"

Presumably that’s JFP’s numbering scheme for electronically published articles.

> p12 (in Van Muylder ref.) "[8](POPL)"

That’s the PACMPL volume number.

> Referee: 2
>
> Comments to the Author
>
> -- Synopsis
>
> This paper revisits Richard Bird's work on 'Zippy tabulations' in the
> context of Agda. Bird's paper shows how to define two different
> traversals of lists by repeatedly removing one element -- one traversal
> is bottom up, the other is top down. In particular, the 'bottom up'
> version avoids recomputation and may be more efficient. This paper shows
> how to use _dependent types_ to clarify the invariants underlying the
> 'binomial tree' used to store intermediate results in the bottom up
> computation. The proof that the bottom up and top down algorithms
> produce the same results given in the paper uses parametricity to
> observe that induction principles are unique -- and therefore the two
> induction principles are extensionally equal.
>
> -- Review
>
> Overall, this pearl is promising, demonstrating the construction of
> Bird's (quite confusing!) BT type. The pearl is a good example of how
> dependent types may make implicit structure more explicit. Having said
> that, however, I found the presentation difficult to follow in places
> (despite some familiarity with Bird's work) - I've tried to give several
> suggestions for simplification and clarification below.
>
> As it stands, the pearl has two main results: the dependent types help
> clarify Bird's BT type; parametricity guarantees uniqueness of induction
> principles. This proof that the bottom up and top down algorithms
> coincide relies (quite heavily) on parametricity, which requires a
> rather subtle justification. Given that the types involved are
> non-trivial, the entire construction is not so easy to follow. For a
> pearl, however, it might be more instructive to lead with a simpler
> example of applying parametricity and/or provide further background and
> explanation. As it stands, the proof is rather underwhelming and seems
> quite disjoint from the rest of the paper: I would have hoped that the
> dependent types introduced helped structure an elementary proof. If the
> main message of the paper is to demonstrate how parametricity guarantees
> unicity -- a simpler motivating example might really help drive this
> point home.

See reply to editor’s comment above.

> In summary, I believe this work may result in a rather nice pearl, but
> the main results deserve better exposition and motivation.
>
> -- Detailed suggestions
>
> Section 1
>
> - The trees in Figure 1 and 2 are not so easy to understand. Would it
>  make sense to add directional arrows? One should be read bottom to
>  top; the other from top to bottom.

[TODO]

* Distracting for Fig. 1

> - 'expected definitions' - perhaps 'definitions you/one would expect'?

Changed.

> - 'representing level n' - this remark did not make sense to me upon
>  first reading. Would help to draw Figure 2 'upside down' -- with h ""
>  at the root? Then it is more clear that upgrade adds a new layer of
>  elements to the leaves of an existing tree.

[TODO]

* That would make the bottom-up algorithm going top-down…
* Not really a tree…

> Section 2 & 3
>
> - A picture or sketch might help clarify the steps in the computation:
>
>  subs : List A -> List (List A)
>  map f : List (List A) -> List B
>  f : List B -> B
>
> In this way, it became more clear to me that composing these functions
> together leads to the desired List A -> B computation.

Presumably this is about spec (1) in Section 1.  We’ve revised the paragraph.

> - I am not convinced that Drop^R should include the natural number
>  index. Wouldn't it be easier to define a relation between lists that
>  drops one element? This seems to be the central relation used to step
>  through the computations. The sublist relation between lists is then
>  the reflexive transitive closure of this relation; computing a given
>  level iterates this relation n-times.

See reply to editor’s comment above.

>  Furthermore, the td algorithm
>  (Section 3) then amounts to the proof that (the transitive closure of)
>  this relation is well-founded. It would be nice if this proof could
>  avoid the additional 'length proof' argument -- which seems
>  unneccessary to me. Proving well-foundedness should be relatively
>  straightforward, as the length of lists decreases in every step.

[TODO]

* Not sure what you mean

> - The line of thought starting around line 140 confused me. Don´t you
>  need a base case for the induction principle?

[TODO]

* Analogy with strong induction on natural numbers

>  The introduction of
>  relative monads and their codensity representation was not well
>  motivated.

See reply to editor’s comments above.

>  The remarks regarding existential/universal quantification
>  deserve further clarification -- drop n xs {{monoid U bot}} isn't
>  existentially quantifying, but rather states that ys arises as a
>  sublist of xs by dropping n elements. Unlike the 'universal
>  quantification' -- that uses an arbitrary P -- the 'existential'
>  version is making a statement over sublists rather than any
>  predicate. It wasn't until the end of the section (the definition of
>  ImmediateSublistInduction) that the point became clear to me.

[FIXME]

* Clarify (conjunction vs disjunction etc)

> - I find the derivation of Drop from Drop^R rather roundabout via
>  relative monads, monoids, codensity representations, etc. Once you
>  have established that Drop^R n xs characterises the sublists at level
>  n -- it seems to me that the Drop data type then corresponds to the
>  memoised version of the relation that drops one element. Hinze's et
>  al.'s Type indexed data types presents the generic (but non-indexed)
>  construction.

[FIXME]

* Rewrite
* Hinze et al.’s paper doesn’t seem related

> - At the end of section two, there are several references to formula
>  2.1. Shouldn't this be 2.2? If so, I'd suggest keeping the two
>  formulas more similar (leaving out implicit arguments A and P in both
>  definitions).

[TODO]

* induction hypothesis List B -> B becomes 2.2

> - line 214: to understand which - grammar.

The sentence has been revised.

> Section 4
>
> The presentation of the bottom-up algorithm is very much top-down. Once
> again, I struggled to grasp the details as functions where used before
> being defined; I, for one, need the type of functions like 'retabulate'
> and 'f' to understand definitions such as bu' (line 266).

[FIXME]

* Really needs a top-down presentation; mark more clearly which are forward references

> Contrary to what I'd expect, the 'counting' still happens 'top down'
> rather than bottom up. For example, the 'base' case tries to drop more
> elements than the list has -- whereas I would expect the base case for
> the bottom up algorithm to start with an empty list and repeatedly
> insert elements. I feel this is a missed opportunity: the two algorithms
> behave differently, but the current presentatioun uses natural numbers in
> the same direction, rather than exploiting the symmetric structure
> in the relation that removes/inserts elements.

[TODO]

* We have a worked solution and the paper reports it

> Section 5
>
> - I'm a bit surprised by the route taken to establish that td and bu are
>  extensionally equal. I realise that rehashing Mu's proof is perhaps
>  not so interesting -- but with the current presentation, makes it seem
>  like there is nothing to prove. I may be mistaken, but I seem to
>  remember not all parametricity results are provable in Agda -- it
>  would be worth spelling out what parts of the construction are proven
>  and what postulates exist (if any).

[FIXME]

* Reply to editor
* Summary in the paper (of the supplementary Agda code)

>  If an important part of the paper is establishing that induction
>  principles are unique -- perhaps it might be worth illustrating this
>  technique on a smaller example first: could you, for example, prove
>  foldl and foldr are equivalent on associative operators? Would that
>  help illustrate the ideas? As it stands, the parametric and
>  higher-order auxiliary types (such as UnaryParametricity
>  ComputationRule) are rather non-trivial -- making it hard to follow
>  the argument regarding the correctness of the construction. Richard
>  Bird's advice for pearl reviews suggests stopping when 'too much
>  specialist knowledge is needed' -- and I felt dangerously close to
>  stopping in this section. The paper could be greatly improved by
>  explaining the principles and construction on a simpler example first
>  in greater detail.

See reply to editor’s comments above.

> - The formatting around line 340 is quite strange. I struggled to parse
>  the definition. Why not move the type of g to a new line?

[FIXME]

* Explain layout
* More arrows

> Referee: 3
>
> Comments to the Author
> The paper tackles the problem of recursion over immediate sublists, that is
> lists with exactly one element removed. A challenge, which is nicely explained
> visually early on, is that a naive solution involves a lot of recomputation
> because across a whole computation, sublists will appear multiple times.
> Earlier work has shown how to solve this problem, although with a cryptic
> definition, and this paper attempts to shed some light on the solution by
> tackling the problem with precise types in Agda.
>
> I thought this was a nice piece of work, and a well-presented and well-written
> paper. It certainly seems to fit as a functional pearl, in that it begins with
> an annoying problem (which, at least to me, is the puzzling definition of the
> bottom up algorithm for implementing the recursion scheme) and using precise
> indexed types both to explain the algorithm and guide its development.
>
> As a really neat example of how dependent types can be used to help
> our understanding of a problem, I'd like to see this
> published. There's a few little things that come up in passing, such
> as the definition of Drop as a data type which illustrate tricks that
> are worth remembering while programming with dependent types. So, maybe with
> some small edits, I'd like to see this accepted.
>
> I have some minor observations - some were made on a first read through and
> it became clear what was going on later. I'm leaving these in my notes though
> because of the way a functional pearl is typically read, so perhaps they will
> be helpful.
>
> 36: It wasn't immediately obvious to me why h : List A -> B

The paragraph has been revised based on Referee 2’s suggestion.

> 68: Why is it impossible to represent each level as a list?

See reply to the same question from Referee 1.

> 69: Maybe illustrating how one of the levels looks as a BT would be useful.

[FIXME]

* A figure from Mu [2024] or just an Agda term

> 87: "If you feel puzzled by 'upgrade' so were we" - this gave me a chuckle.

The kind of reaction we want!

> Why is it not valid Agda though? Is this about termination checking?

See reply to the same question from Referee 1.

> 90: I looked up the Bird paper, for context, and almost missed the footnote
> saying that he called it 'cd'. It might help to put that in the main text. I also wonder
> why it's called 'cd'.

[FIXME]

* Doesn’t really need to read Bird’s paper
* Presumably inversion of dc (not in our paper)

> 160: {{ }} marks an instance argument, right?

Yes.  This is now mentioned in the text.

> 168: I probably wouldn't mention the monoid laws if they're not needed, but
> perhaps some readers who are more experience Agda users will wonder anyway!

[FIXME]

* Similar question

> 185: This definition of DropR could use a bit more explanation. Although
> I think I might just be being distracted by the Agda instance argument
> notation.

[FIXME]

* Add a bit of explanation

> 203: I found this observation (Drop is an indexed version of BT, with
> empty trees) interesting (I expect I was supposed to!). Especially to see
> the number of elements dropped in each branch.

[FIXME]

* Maybe worth foreshadowing (to motivate Drop as a precise version of BT)

> 220: Does this have the same problem as (1.1) that it recomputes for
> sublists? It seems that it would.

Yes.

> 285: A nitpick, maybe a pet peeve, but for "just follow the types",
> I'd drop "just". But it's nice that the setup means that the
> implementation is pretty much entirely type directed.

Dropped.

> 300: This is probably a personal preference, but if 'n' needs to be present
> at runtime, maybe it's clearer as an explicit argument.

[FIXME]

* OK

> 332: This is pleasing, and to me is another small example of why it's
> worth tackling this problem in a depenently typed setting (and what precise
> types can offer).

Thanks!
