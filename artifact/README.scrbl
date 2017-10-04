#lang scribble/manual

@require[scribble/eval
         scriblib/autobib
         racket/list
         #;(for-label (only-in rosette define-symbolic))]

@(define HOME (find-system-path 'home-dir))
@(define REPO (apply build-path (drop-right (explode-path (current-directory)) 1)))
@(define ARTIFACT (build-path REPO "artifact"))
@(define TURNSTILE (build-path REPO "turnstile"))
@(define MACROTYPES (build-path REPO "macrotypes"))
@(define DOCS (build-path TURNSTILE "doc" "turnstile" "index.html"))
@(define GUIDE (build-path TURNSTILE "doc" "turnstile" "The_Turnstile_Guide.html"))
@(define REF (build-path TURNSTILE "doc" "turnstile" "The_Turnstile_Reference.html"))
@(define POPL-EXAMPLES (build-path ARTIFACT "examples"))
@(define RACKET-EXAMPLES (build-path MACROTYPES "examples"))
@(define TURNSTILE-EXAMPLES (build-path TURNSTILE "examples"))
@(define TURNSTILE-TEST (build-path TURNSTILE-EXAMPLES "tests"))
@(define MLISH-TEST (build-path TURNSTILE-TEST "mlish"))
@(define (EXAMPLE f) (list "runnable program: " (file-url POPL-EXAMPLES f)))

@(define PAPER-TITLE  "Symbolic Types for Lenient Symbolic Execution")
@(define PAPER-PDF  "paper.pdf")
@(define PAPER (build-path ARTIFACT PAPER-PDF))

@(define REPO-URL "https://github.com/stchang/typed-rosette/tree/master/typed/rosette")
@(define POPL-URL "http://www.ccs.neu.edu/home/stchang/popl2018")
@(define VM-URL (string-append POPL-URL "/" "typed-rosette.ova"))

@(define (file:// p) ;; Path -> String
   (string-append "file://" (path->string p)))

@(define (file-url prefix [suffix #f]) ;; Path (U String #f) -> Elem
   (define p (if suffix (build-path prefix suffix) prefix))
   (hyperlink (file:// p) (tt (if suffix suffix (path->string p)))))

@; -----------------------------------------------------------------------------

@title{Artifact: @|PAPER-TITLE|}

@(author (author+email "Stephen Chang" "stchang@ccs.neu.edu")
         (author+email "Alex Knauth" "alexknauth@ccs.neu.edu")
         (author+email "Emina Torlak" "emina@cs.washington.edu"))

This is a README file for the artifact that accompanies "@|PAPER-TITLE|" in
POPL 2018. If you have any questions, please email the first two authors.

Our artifact is a VM image that contains:
@itemlist[
  @item{a revised version of the submitted paper @hyperlink[@file://[PAPER]]{[link]},}
  @item{a distribution of the Racket programming language (v6.10.1),}

  @item{and a prototype implementation of the Typed Rosette language and some
        of its libraries.}
  ]

The goal of this artifact is to
provide a tour of the Typed Rosette language and parts of its
implementation, primarily by examining runnable versions of the paper's examples.


@; -----------------------------------------------------------------------------
@section{Artifact Setup and Installation}

Skip this section if you are already reading this document from within the VM.

The artifact may be installed in two ways:
@itemlist[@item{@secref{vm} (recommended)}
          @item{@secref{manual}}]

The VM image is configured to automatically login to the @tt{artifact} user
account. The password for the account is also @tt{artifact}. The account has
root privileges using @tt{sudo} without a password.


@subsection[#:tag "vm"]{VirtualBox VM image}

The artifact is available as a virtual machine appliance for
@hyperlink["https://www.virtualbox.org/wiki/Downloads"]{VirtualBox}.
@margin-note{VM appliance:
@hyperlink[VM-URL]{[link]}}

To run the artifact image, open the downloaded @tt{.ova} file using the
@tt{File->Import Appliance} menu item. This will create a new VM
that can be launched after import. We recommend giving the VM at least
2GB of RAM.

@subsection[#:tag "manual"]{Manual installation}

Follow these instructions to manually install the artifact only if
the VirtualBox image is somehow not working.

(We have only tested these steps with Linux.)

@itemlist[@item{Install @hyperlink["http://download.racket-lang.org"]{Racket
            6.10.1}.

           Add the Racket @tt{bin} directory to your @tt{PATH}. The
           remaining steps assume that Racket's @tt{bin} directory is in the 
           @tt{PATH}.}
           
          @item{Clone the @tt{typed-rosette} repository into the @tt{popl2018} directory
                (or any directory):

                @tt{git clone https://github.com/stchang/typed-rosette popl2018}}
          @item{Change directory to the repository root:

                @tt{cd popl2018}}
          @item{From the repository root, check out the @tt{popl2018-artifact} branch:

                @tt{git checkout popl2018-artifact}}
          @item{From the repository root, install the repo as a Racket package:

                @tt{raco pkg install }@literal{--}@tt{auto -n typed-rosette}}
          @;item{Register the documentation:

                @;tt{raco setup }@literal{--}@tt{doc-index}}
          @item{From the repository root, change to the @tt{artifact} directory:

                @tt{cd artifact}}
          @item{Build the readme:

                @tt{make readme}}
          @item{Open the produced @tt{README.html} file.}]

@; -----------------------------------------------------------------------------
@section{Artifact Overview}


The following files may also be accessed via the VM Desktop:
@itemlist[
  @item{@file-url[ARTIFACT]{README.html}: This page}
  @item{@file-url[ARTIFACT PAPER-PDF]: The camera-ready version of the paper.}
  @item{@tt{DrRacket}: DrRacket IDE for Racket v6.10.1

  Run example files by opening them in DrRacket and pressing the "Run" button.
  
 Alternatively, run files from the command line with @tt{racket} (may be faster):

  @tt{racket <Racket filename>}

  A terminal window may be opened from the launcher bar at the bottom of the
virtual desktop (second icon from the left).

  Most of the examples described in this artifact can be found at @file-url[POPL-EXAMPLES]{}
  }
 ]


@; -----------------------------------------------------------------------------
@section[#:tag "typed-rosette"]{Typed Rosette}

This artifact is set up to allow exploration of both Typed Rosette's
implementation and usage.

Some examples of Typed Rosette programs can be found in the test suite, viewable here:
@file-url[REPO]{test}.

To run the test suite, open a terminal and execute the following command (may
take 30min to complete):

@tt{raco test -p typed-rosette}

The complete source for Typed Rosette's implementation is viewable at:
@itemlist[
@item{local: @file-url[REPO]{typed/rosette}}
@item{@hyperlink[REPO-URL]{web link}}]

@; -----------------------------------------------------------------------------
@section[#:tag "examples"]{Code From the Paper}

For readability and conciseness, the paper occasionally stylizes or elides code
and thus some examples may not run exactly as presented. This artifact, however,
includes and describes full runnable versions of all the paper's examples.

Some clarifications when reading the code:
@itemlist[
  @item{Symbolic types in the @emph{paper} are decorated with a Latex @tt{\widehat}
        while concrete types are undecorated. Somewhat confusingly, @emph{Typed Rosette code}
        uses these same undecorated type names to represent symbolic values, while
        concrete types have a @tt{C} prefix.
 
        For example:
        @tabular[#:style 'boxed
                 (list (list @bold{Description} @bold{Paper} @bold{Typed Rosette Program})
                       (list "type for (possibly) symbolic integers" @tt{\widehat{Int}} @tt{Int})
                       (list "type for concrete integers" @tt{Int} @tt{CInt}))]}

@item{The @tt{C} prefix convention is used for both concrete base types as well as
concrete type constructors in Typed Rosette.}
]

NOTE: The file links in the following subsections open in the browser by default. (If
not viewing in the VM, you may need to adjust your browser's "Text Encoding" to
display Unicode.) To run the files, run with @tt{racket} on the command line,
or open with DrRacket.


@; ----------------------------------------------------------------------------
@; paper section 1
@subsection{Paper section 1}

The first section of the paper uses a one-line example to illustrate the main
difficulty with lenient symbolic execution that we tackle in the
paper. Specifically, when symbolic values mix with code that may not recognize
them, unexpected results (that are difficult to debug) may occur. Here is the
same example, with more comments, in (untyped) Rosette:

@codeblock{
#lang rosette
 
(define-symbolic x integer?) ; defines symbolic integer x
 
;; evaluates to symbolic value (+ x 1)
;; works because Rosette's `integer?` returns true for symbolic ints
(if (integer? x)
    (add1 x)
    (error "can't add non-int"))
 
;; import raw Racket's `integer?`, as `unlifted-int?`
(require (only-in racket [integer? unlifted-int?]))
 
;; errors bc `unlifted-int?` does not recognize symbolic vals and returns false
(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int"))
}

This full runnable program may also be viewed here: @file-url[POPL-EXAMPLES]{intro-example-untyped-rosette.rkt}

The programmer expects this program to reach the "then" branch, and this is the
case in the first @racket[if] expression because Rosette's @racket[integer?]
function recognizes symbolic values.

The second @racket[if] expression is identical to the first except it uses a
different predicate @racket[unlifted-int?]. Lenient symbolic execution
increases expressiveness because it allows mixing of lifted and unlifted code, but if
a programmer mistakenly uses such an unlifted predicate (which won't always
have a convenient name like @racket[unlifted-int?]) that does not recognize
symbolic values, evaluation reaches the error branch.

This kind of error is common in a language that supports lenient symbolic
evaluation like Rosette. Worse, this kind of error is particuarly difficult to
debug because the program often fails silently by simply returning the wrong
answer. For example if the "else" branch above returned a result instead of
throwing an error, then a programmer may not even be aware of a problem unless
they inspect the output.

Typed Rosette helps lenient symbolic execution by reporting these problems---
when symbolic values flow to positions that do not recognize them---as type
errors:

@codeblock{
#lang typed/rosette
 
(define-symbolic x integer?) ; defines symbolic integer x
 
;; evaluates to symbolic value (+ x 1)
;; works because Rosette's `integer?` returns true for symbolic ints
(if (integer? x)
    (add1 x)
    (error "can't add non-int"))
 
;; import raw Racket's `integer?`, as `unlifted-int?`, with type
(require/type racket [integer? unlifted-int? : (C→ CAny CBool)])
 
;; type error
(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int"))
}

This typed program is viewable here: @file-url[POPL-EXAMPLES]{intro-example-typed-rosette.rkt}

In this program, the raw Racket @racket[unlifted-int?] is imported with a
@racket[CAny] input type, indicating that its input must be a @emph{concrete}
value. Since @racket[x] is a symbolic value, the type checker raises a type error:

@codeblock{
;; intro-example-typed-rosette.rkt:15.4: #%app: type mismatch
;;   expected:    CAny
;;   given:       (Constant (Term CInt))
;;   expressions: x
;;   at: (#%app unlifted-int? x)
}

In addition to reporting the error location, this message provides extra
information by revealing a few internal details of Typed Rosette, namely that
Typed Rosette actually recognizes multiple variants of each symbolic type from
paper. Specifically, a symbolic @tt{Int} type is represented internally as the
@tt{(Term CInt)} seen in the error message, where a @tt{Term} constructor wraps
a concrete @tt{CInt} type to convert it into a symbolic type. In
addition, a @tt{Constant} type constructor represents symbolic constant
values (which are produced with @racket[define-symbolic]), e.g., in the above
program, @racket[x] is a symbolic constant but the symbolic value @racket[(+ x
1)] result of @racket[(add1 x)] is not.


@; ----------------------------------------------------------------------------
@; paper section 2
@subsection{Paper section 2}

The paper's second section introduces more of Rosette via examples and further
motivates the need for Typed Rosette.

Each subsequent subsection first links to a runnable program file, and then
comments on the contents of the file.

@subsubsection[#:tag "safe-example"]{Safe Examples}

@EXAMPLE{sec2-rosette-safe-examples.rkt}

The first few examples in section 2 of the paper introduce basic computing with
symbolic values in Rosette and show examples of interacting with the solver,
for example to verify the sortedness of a vector given some constraints. These
examples use the restricted @tt{rosette/safe} language where all language forms
are lifted to recognize symbolic values, i.e., no lenient symbolic execution is
allowed. These "safe" programs are mostly straightforward so we will not repeat
the explanations here.

@subsubsection[#:tag "unsafe-example"]{Unsafe Example}

@EXAMPLE{sec2-rosette-unsafe-hash-example.rkt}

The full @racket[rosette] language supports lenient symbolic execution, i.e.,
the language is more convenient and expressive because programmers may use the
full Racket language which includes unlifted constructs and data structures
that may be too complicated to encode as solver constraints. The full Rosette
language is unsafe, however, because programmers must manually concretize
symbolic values before they reach unlifted positions.

This example, similar to the vector example from the @secref{safe-example}
section, tries to verify "sortedness" of a hash table, where the concrete
integer keys act as the "indices". Even though we use the same constraints as
before, the solver returns a "counterexample" that supposedly violates our
sortedness specification. Inspecting this "counterexample", however, reveals
that it is not actually a counterexample---instantiating our program with the
variable assignments still results in a sorted hash.

At this point, Rosette programmers are often stumped, since the solver has
returned an incorrect result but the programmer has no information with which
to look for the cause of the problem in the program. In other words, the
program has failed silently. An inattentive programmer may not even think
anything is wrong and instead accept the result of solver as correct. This
highlights the main problem with lenient symbolic execution, which we solve
with a type system.

@subsubsection{Unsafe Example, with Types}

@EXAMPLE{sec2-typed-rosette-hash-example.rkt}

The problem in the @secref{unsafe-example} is that hash tables are unlifted;
specifically @racket[hash-ref] does not recognize symbolic values but is given
one. Typed Rosette is able to detect this problem and reports it as a type
error, pinpointing the exact source of the problem:

@codeblock{
;; sec2-typed-rosette-hash-example.rkt:13.19: hash-ref: type mismatch: expected CInt, given (Constant (Term CInt))
;;   expression: i
;;   at: i
;;   in: (hash-ref h i)
}

@subsection{Paper section 3}

@subsubsection{Basic Occurrence Typing}

@EXAMPLE{sec31-basic-occurrence-typing.rkt}

These examples demonstrate basic occurrence typing. The input to the @racket[f]
function, @racket[x], may be either a (concrete) integer or string. The 
@racket[integer?] predicate then refines @racket[x] to an integer and string in
the "then" and "else" branches, respectively.

The @racket[g] function shows that the predicate's argument may be an arbitrary
expression and is not restricted to plain variables. Nevertheless, @racket[x]'s
type is refined in the same way as in @racket[f]. (We use @racket[and] with a
single argument to stand in for the @tt{id} function mentioned on page 6 of the
paper.)

@subsubsection{Path Concreteness: Motivation}

@EXAMPLE{sec34-path-concreteness1-untyped.rkt}

This example motivates the need for path concreteness when mutation is
involved. Specifically, a concrete value, even if it is only ever assigned
other concrete values, may change into a symbolic value if the mutation occurs
under a symbolic path.

@EXAMPLE{sec34-path-concreteness1-typed.rkt}

Our type system rejects mutation of concrete variables in symbolic paths
because it results in unsoundness. In other words, allowing such mutations
results in variables with concrete types having symbolic values.

A programmer wishing to allow such mutations may annotate the variable with a
possibly symbolic type, like @racket[y] in the example.

@subsubsection{Path Concreteness: Functions}


Functions that mutate variables add extra complication since they require the
type checker to be context sensitive at function call sites. Specifically, the
type checker must track whether a function (that mutates variables) is
@emph{called} in a symbolic path or a concrete path. Typed Rosette addresses
this in two ways.

@itemlist[#:style 'ordered

@item{@file-url[POPL-EXAMPLES]{sec34-path-concreteness2.rkt}

Bodies of functions defined with @racket[define] are type checked twice, once
assuming concrete path and once assuming symbolic path. The @racket[f] function
in the example type checks because the variable it mutates, @racket[y], is
symbolic and thus it is safe to call @racket[f] in either a concrete or
symbolic path.

In contrast, the @racket[g] function in the example is rejected because
@racket[x] has a concrete type and thus allowing calls to @racket[g] it in a
symbolic path is unsound.}

@item{@file-url[POPL-EXAMPLES]{sec34-path-concreteness3.rkt} Programmers may
also restrict where a function may be called by defining it with
@racket[define/conc]. Such functions may only be called in a concrete path. In
this example, we define the same @racket[g] function as in the first item, only
we use @racket[define/conc]. Thus the @emph{definition} now type checks, but
attempting to @emph{call} this @racket[g] function in a symbolic path results
in a type error.}]



@section{Typed Rosette Implementation}

This section contains commentary for examples from section 5 of the paper.

To help readability, some examples in this section may utilize a type checker
unit-testing framework, evident from a @racket[(require typed/lib/roseunit)] at
the top of the file. A programmer using the unit-testing framework may write
three kinds of tests:

@itemlist[
@item{A @racket[(check-type e : τ)] test passes if @racket[e]'s type typechecks with type @racket[τ].}
@item{A @racket[(check-not-type e : τ)] test passes if @racket[e]'s type does not typecheck with @racket[τ]. This kind of test is particularly useful in languages with subtyping.}
@item{A @racket[(typecheck-fail e)] test passes if @racket[e] fails to type
check. This form may additionally specify a regexp that the produced error message must satisfy.}]

When running a file that contains these tests, an error message is produced for
failing tests, and no output is produced if all tests pass.

@subsection{Sample Type Rule Implementations}

We created Rosette using Turnstile, a Racket-based meta-DSL for creating typed
languages. Turnstile allows implementing type rules with a declarative syntax
that resembles mathematical type rule specifications.

@margin-note{NOTE: The details of the Turnstile language are not the focus of
this paper but, briefly, Turnstile programmers implement typed languages by
writing interleaved rewrite-and-typecheck judgements of the form @tt{Γ ⊢ e ≫
e+ (⇒ key val) ...} or @tt{Γ ⊢ e ≫ e+ (⇐ key val) ...}, where @tt{⇒} and @tt{⇐}
are the standard "synth" and "check" bidirectional arrows, respectively. A rule
may specify more than one key-value pair and in the example rules, we utilize
this to simultaneously check types and propositions, as specified in section 3
of the paper. In addition, the @tt{e ≫ e+} part of the relation specifies that
@tt{e} rewrites to @tt{e+}.}

Figure 25 of the paper shows a few example type rules. These same rule
implementations may be viewed in the Typed Rosette repo here (the syntax has
evolved slightly but the essence remains the same):

@itemlist[
@item{@hyperlink["https://github.com/stchang/typed-rosette/blob/master/typed/rosette/bool.rkt#L24-L51"]{@tt{if} rule}

@itemlist[@item{In the first, concrete, case, the path concreteness is unchanged and is thus inherited from the context.}
@item{In the second, symbolic case, the path concreteness is changed to symbolic.}]}

@item{@hyperlink["https://github.com/stchang/typed-rosette/blob/master/typed/rosette/base-forms.rkt#L901-L908"]{@tt{set!} rule}

The implementation of the @racket[set!] mutation rule differs slightly from the
paper because the two separate cases shown in the paper are combined into one
in the implementation. In place of a separate clause, the @racket[no-mutate?]
function (whose implementation can be seen
@hyperlink["https://github.com/stchang/typed-rosette/blob/master/typed/rosette/types.rkt#L176-L177"]{here}),
determines when mutation of the @racket[x] variable is not allowed (when
@racket[x] has a concrete type and the path is symbolic), and raises a type
error if appropriate.}  ]

@subsection{Concreteness Polymorphism in Practice}

@EXAMPLE{sec53.rkt}

Section 5.3 of the paper shows an example of how programmers may control the
precision of the type checker. Specifically, the @racket[Ccase->] type is the
implementation of the intersection type specified in section 3.3 of the
paper. When applying a function with a @racket[Ccase->] type, the type checker
checks each consituent function type, in listed order, and either uses the
first one that type checks, or raises a type error if all the
options are exhausted.

Function types also support specifying optional arguments, as seen in the
@racket[add/opt] example.

@subsection{Handling Imprecision}

@EXAMPLE{sec54.rkt}

Section 5.4 shows an example where the programmer may need to add
annotations to help the type checker accept valid programs.

The first example shows an instance where evaluating an expression @racket[(if
b 2 2)] results in a concrete value, but the type system computes a symbolic
type. In this case, a programmer can use @racket[term?] (equivalent to
@tt{conc?} on page 11 of the paper) and occurrence typing to refine the type.

The second example shows an instance where the type system computes a union
type, but the runtime value is more precise (due to Rosette's infeasible path
pruning). In this case, a programmer can use @racket[assert-type], which
behaves somewhat like casts in some OO languages in that it refines the type
but preserves safety by inserting runtime checks. In Rosette, it results in an
extra constraint for the solver. In this example, the @racket[assert-type]
generates the constraint that the symbolic boolean @racket[b] must be
@racket[true].


@section{Evaluation}

@subsection{Synthesizing Loop-Free Bitvector Programs}

@EXAMPLE{bv.rkt}

This tiny example shows usage of a bitvector constructor @racket[bv] with both
concrete and a symbolic integer values. Since @racket[bv] requires a concrete
argument, the former evaluates properly while the latter results in a type error.

The paper also describes a @tt{mk-trailing-0s} example. The same example in our
test suite may be viewed
@hyperlink["https://github.com/stchang/typed-rosette/blob/master/test/bv-ref-tests.rkt#L305-L308"]{here}.

This test file may be run by navigating to the containing directory and running
the command (may take 5 minutes to complete):

@tt{racket bv-ref-tests.rkt}

NOTE: Running the Typed Rosette test suite, as described in the
@secref{typed-rosette} section above, runs this bitvector test suite as well.



@subsection{A Library for Relational Logic Specifications}
@subsubsection{Untyped}
untyped example (see following note): @file-url[POPL-EXAMPLES]{cats-untyped.rkt}

@margin-note{NOTE: This untyped file cannot be run by default in this VM due to
package name conflicts. Specifically, the VM has the typed Ocelot package
installed while the above file uses the untyped package. It's not too important
to do this, but to get the above untyped file to run, execute the following
commands from the @tt{popl2018-artifact} directory:

@itemlist[
@item{remove typed package: @tt{raco pkg remove ocelot}}
@item{install untyped package: @tt{raco pkg install -n ocelot untyped-ocelot/}}
@item{run the untyped example above: @tt{racket typed-rosette/artifact/examples/cats-untyped.rkt}}
@item{uninstall untyped package: @tt{raco pkg remove ocelot}}
@item{re-install typed pacakge: @tt{raco pkg install ocelot/}}]}

The details of this particular example (taken from the documentation) is not
too important. The main takeaway is that the untyped file demonstrates (again) what
happens if a programmer accidentally gives an unlifted function a symbolic
value: the program silently fails by returing the wrong answer.

Further, the source of the problem,
@hyperlink["https://github.com/stchang/ocelot/blob/master/engine/interpretation.rkt#L45"]{which
can be seen here}, is very similar to the example from page 1 of
the paper. Specifically, the program branches (the @racket[#:when x] from the
link) on a value that is assumed to be concrete, but supplying a symbolic value
causes a different branch to execute. In this case, the list comprehension does
not properly filter out the undesired cases.

@subsubsection{Typed}
@EXAMPLE{cats-typed.rkt}

The typed version raises a type error when the unlifted function is given a symbolic argument.

To further explore the typed version of the ocelot library, one can start by
@hyperlink["https://github.com/stchang/ocelot/tree/typed-rosette/test"]{looking
at the test suite}. To run the typed ocelot test suite (assuming the typed
version of the package is installed), execute the command:

@tt{raco test -p ocelot}

@subsection{Synthesizing Incremental Algorithms}

@EXAMPLE{incremental.rkt}

The paper (and the @tt{incremental.rkt} file above) describes two
representative examples that illustrate the kind of techniques required to port
the Incremental language to Typed Rosette.

This section will describe the techniques, and then point out an instance in
the real implementation code where the technique is used. The instances we
point out will be from this implementation file:
@file-url[REPO]{../incremental/typed/src/rosette/enum-set.rkt}

The first example requires a symbolic type annotation in order to successfully
mutate a vector in a symbolic path. Such annotations are used in the
@racket[enum-make-set] function in the implementation file.

The second example uses occurrence typing to eliminate a "Maybe"-type-like
union with false. Such annotations may be seen in the @racket[enum-make-symbolic-set] function in the implementation file.

Finally, the paper reports that we were able to remove roughly 100 lines of
dynamic checks by porting the library to Typed Rosette. In the
@tt{enum-set.rkt} implementation file, we left in these checks as comments in
many places. For example, the @emph{untyped} version of @racket[enum-make-set]
used a @racket[(when (term? ...) (error ...))] check to prevent symbolic values
from being passed to the function. Such checks are both incomplete, because the
@racket[term?] predicate does not recognize symbolic union values, and
unnecessary in Typed Rosette, where instead we prevent @emph{all} symbolic
values from being passed to the function by specifying types.

To further explore the typed incremental language, one can start by looking at
the test suite files in these directories:

@itemlist[
@item{@file-url[REPO]{../incremental/example/typed/}}
@item{@file-url[REPO]{../incremental/typed/src/test/}}]

To run the Incremental language test suite, execute the command (may require
20-30 minutes to complete):

@tt{raco test -p incremental}
