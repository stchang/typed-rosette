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

@(define REPO-URL "https://github.com/stchang/typed-rosette")
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
POPL 2018.  If you have any questions, please email any (or all) of the
authors.

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
  
 Alternatively, run files from the command line with @tt{racket}:

  @tt{racket <Racket filename>}}
 ]


@; -----------------------------------------------------------------------------
@section[#:tag "typed-rosette"]{Typed Rosette}

This artifact is set up to allow exploration of both Typed Rosette's
implementation and usage.

One source of examples is the Typed Rosette test suite, viewable here: @file-url[REPO]{test}

To run the test suite, open a terminal and execute the following command (may
take 30-60min to complete):

@tt{raco test -p typed-rosette}

The complete source for the implementation is viewable at:
@itemlist[
@item{local: @file-url[REPO]{typed/rosette}}
@item{@hyperlink[REPO-URL]{web link}}]

@; -----------------------------------------------------------------------------
@section[#:tag "examples"]{Code From the Paper}

For readability and conciseness, the paper occasionally stylizes or elides code
and thus some examples may not run exactly as presented. This artifact, however,
includes and describes full runnable versions of all the paper's examples.

Some code clarifications:
@itemlist[
  @item{Symbolic types in the @emph{paper} are decorated with a Latex @tt{\widehat}
        while concrete types are undecorated. Somewhat confusingly @emph{Typed Rosette code}
        uses these same undecorated type names to represent symbolic values, while
        concrete types have a @tt{C} prefix.
 
        For example:
        @tabular[#:style 'boxed
                 (list (list @bold{Description} @bold{Paper} @bold{Typed Rosette Code})
                       (list "type for (possibly) symbolic integers" @tt{\widehat{Int}} @tt{Int})
                       (list "type for concrete integers" @tt{Int} @tt{CInt}))]}
       ]

NOTE: The file links in the following subsections open in the browser by default. (If
not viewing in the VM, you may need to adjust your browser's "Text Encoding" to
display Unicode.) To run the files, run with @tt{racket} on the command line,
or open with DrRacket.


@; ----------------------------------------------------------------------------
@; paper section 1
@subsection{Paper section 1}

The first section of the paper uses one small example to illustrate the main
problem with lenient symbolic execution that we tackle in the paper, where
symbolic values mix with code that may not recognize them. Specifically, here
is the example in (untyped) Rosette:

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

The full runnable program may also be viewed here: @file-url[POPL-EXAMPLES]{intro-example-untyped-rosette.rkt}

The programmer expects the program to reach the "then" branch and this is true
in the first @racket[if] expression because Rosette's @racket[integer?]
function recognizes symbolic values.

The second @racket[if] expression is identical to the first except it uses a
different conditional predicate. Lenient symbolic increases expressiveness by
allowing mixing of lifted and unlifted code, however, so if a programmer
mistakenly uses an @emph{unlifted} predicate (which we've conveniently named
@racket[unlifted-int?] here) that does no recognize symbolic value, evaluation
reaches the error branch.

This kind of error is common in languages supporting lenient symbolic
evaluation like Rosette and is particuarly difficult to debug because the
program often fails silently. For example if the "else" branch above returned a
result instead of throwing an error, then a programmer may not even be aware of
a problem.

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

This program is also available here @file-url[POPL-EXAMPLES]{intro-example-typed-rosette.rkt}

In this program, the raw Racket @racket[integer?] is imported with a
@racket[CAny] type, indicating that its input may be any @emph{concrete}
value. Since @racket[x] is a symbolic value, the type checker raises a type error:

@codeblock{
;; intro-example-typed-rosette.rkt:15.4: #%app: type mismatch
;;   expected:    CAny
;;   given:       (Constant (Term CInt))
;;   expressions: x
;;   at: (#%app unlifted-int? x)
}

In addition to reporting the error, this message provides extra information by
a few internal details of Typed Rosette. Specifically, Typed Rosette actually
tracks multiple variants of each symbolic type from the paper and internally
uses a @tt{Term} constructor to convert a concrete type into a (possibly)
symbolic one, and uses a @tt{Constant} constructor to additionally track
symbolic constant values (which are produced with @racket[define-symbolic]). In
the above program, @racket[x] is a symbolic constant, but the symbolic value
@racket[(+ x 1)] result of @racket[(add1 x)] is not.


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
the language is more expressive because programmers may use the full Racket
language which includes unlifted constructs and data structures that may be too
complicated to encode as solver constraints. The full Rosette language is
unsafe, however, because programmers must manually concretize symbolic values
before they reach unlifted positions.

This example, in the same manner as the safe vector example from the
@secref{safe-example} section, tries to verify "sortedness" of a hash table,
where the keys are concrete integers acting as the "indices". Even though we
use the same constraints as before, the solver returns a "counterexample" that
supposedly violates our sortedness specification. Inspecting
this "counterexample", however, reveals that it is not actually a
counterexample---it still results in a sorted hash.

At this point, Rosette programmers are often stumped, since the solver has
returned an incorrect result but the programmer has no information with which
to look for the cause of the problem in the program. In other words, the
program has failed silently. An inattentive programmer may not even think
anything is wrong and instead accept the result of solver as correct. This
highlights the main problem with lenient symbolic execution.

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
type checker must track whether a function (that mutates variables) is called
in a symbolic path or a concrete path. Typed Rosette addresses this in two
ways.

@itemlist[#:style 'ordered

@item{@file-url[POPL-EXAMPLES]{sec34-path-concreteness2.rkt} Bodies of
functions defined with @racket[define] are type checked twice, once assuming
concrete path and once assuming symbolic path. This example is rejected because
calling it in a symbolic path leads to unsoundness. If a
@racket[define]-defined function type checks, we know it's safe to call in
either a concrete or symbolic path, so we do not need extra checking at the
call sites.}

@item{@file-url[POPL-EXAMPLES]{sec34-path-concreteness3.rkt} Programmers may
also restrict where a function is called by defining it with
@racket[define/conc]. Such functions may only be called in a concrete path. In
this example, we define the same @racket[g] function as as in the first item,
only we use @racket[define/conc]. Thus the definition type checks this
time. But attempting to call this @racket[g] function in a symbolic path
results in a type error.}]



@section{Typed Rosette Implementation}

This section contains commentary for examples from section 5 of the paper.

To help readability, these examples may utilize a special type checker
unit-testing framework, evident from a @racket[(require typed/lib/roseunit)] at
the top of the file. The unit-testing framework has three main forms:

@itemlist[
@item{A @racket[(check-type e : τ)] test passes if @racket[e] has type @racket[τ].}
@item{A @racket[(check-not-type e : τ)] test passes if @racket[e] does not have type @racket[τ].}
@item{A @racket[(typecheck-fail e)] test passes if @racket[e] fails to type
check. This form may additionally specify a regexp that the error message must satisfy.}]

When running a file that contains these tests, an error message is produced for
failing tests, and no output is produced if all tests pass.

@subsection{Sample Type Rule Implementations}

We created Rosette using Turnstile, a Racket-based meta-DSL for creating typed
languages. Turnstile allows implementing type rules with a declarative syntax
that resembles mathematical type rule specifications. Figure 25 of the paper
shows a few example rules. These same rule implementations may be viewed in the
repo here (the syntax has evolved slightly):

@itemlist[
@item{@hyperlink["https://github.com/stchang/typed-rosette/blob/master/typed/rosette/bool.rkt#L24-L51"]{@tt{if} rule}

@itemlist[@item{In the first, concrete, case, the path concreteness is unchanged and is thus inherited from the context.}
@item{In the second, symbolic case, the path concreteness is changed to symbolic.}]}

@item{@hyperlink["https://github.com/stchang/typed-rosette/blob/master/typed/rosette/base-forms.rkt#L901-L908"]{@tt{set!} rule}

The implementation of the @racket[set!] mutation rule does not actually need
two separate cases like shown in the paper. Instead, the @racket[no-mutate?]
function (whose implementation can be seen
@hyperlink["https://github.com/stchang/typed-rosette/blob/master/typed/rosette/types.rkt#L176-L177"]{here}),
determines when mutation of the @racket[x] variable is not allowed (when
@racket[x] has a concrete type and the path is symbolic), and raises a type
error if appropriate.}
]

NOTE: The details of the Turnstile language are not the focal point of this
paper but, briefly, programmers write interleaved rewrite and type check
judgements of the form @tt{Γ ⊢ e ≫ e+ (⇒ key val) ...} or @tt{Γ ⊢ e ≫ e+ (⇐ key
val) ...}, where @tt{⇒} and @tt{⇐} are the conventional "synth" and "check"
bidirectional arrows, respectively. A rule may specify more than one key-value
pair and in the example rules, we utilize this to simultaneously check types
and propositions, as shown in section 3 of the paper. In addition, the @tt{e ≫
e+} part of the relation specifies that @tt{e} rewrites to @tt{e+}.

@subsection{Concreteness Polymorphism in Practice}

@EXAMPLE{sec53.rkt}

Section 5.3 of the paper shows an example of how programmers may control the
precision of the type checker. Specifically, the @racket[Ccase->] type is the
implementation of the intersection type specified in section 3.3 of the
paper. When applying a function with a @racket[Ccase->] type, the type checker
checks each consituent function type, in listed order, and either uses the
first one that type checks or raises a type error if it exhausts all the
options.

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
type, but the runtime value is more precise (due to Rosette's path pruning). In
this case, a programmer can use @racket[assert-type], which is behaves somewhat
like casts in some OO languages in that it refines the type but "preserves"
soundness by inserting runtime checks. In Rosette, it results in an extra
constraint for the solver. In this example, the @racket[assert-type] generates
the constraint that the symbolic boolean @racket[b] must be @racket[true].


@section{Evaluation}

@subsection{Synthesizing Loop-Free Bitvector Programs}

@EXAMPLE{bv.rkt}

This tiny example shows usage of a bitvector constructor @racket[bv] with both
concrete and a symbolic integer values. Since @racket[bv] requires a concrete
argument, the former evaluates properly while the latter results in a type error.

The paper also describes a @tt{mk-trailing-0s} example. The same example in our
test suite may be viewed
@hyperlink["https://github.com/stchang/typed-rosette/blob/master/test/bv-ref-tests.rkt#L305-L308"]{here}.

This test file may be run by navigating to the containing directory and running the command:

@tt{racket bv-ref-tests.rkt}

NOTE: Running the Typed Rosette test suite, as described in the
@secref{typed-rosette} section above actually runs test suite for this
bitvector example as well.



@subsection{A Library for Relational Logic Specifications}
@subsubsection{Untyped}
untyped example (see note below): @file-url[POPL-EXAMPLES]{cats-untyped.rkt}

NOTE: This untyped file cannot be run by default in this VM due to package name
conflicts. Specifically, the VM has the typed Ocelot package installed while
the above file uses the untyped package. It's not too important, but to run the
above untyped file (from the @tt{popl2018-artifact} directory:

@itemlist[
@item{remove typed package: @tt{raco pkg remove ocelot}}
@item{install untyped package: @tt{raco pkg install -n ocelot untyped-ocelot/}}
@item{run the untyped example above: @tt{racket typed-rosette/artifact/examples/cats-untyped.rkt}}
@item{uninstall untyped package: @tt{raco pkg remove ocelot}}
@item{re-install typed pacakge: @tt{raco pkg install ocelot/}}]

The untyped file again demonstrates that if a programmer accidentally gives an
unlifted function a symbolic value, the program silently fails by returing the
wrong answer.

In fact, the
@hyperlink["https://github.com/stchang/ocelot/blob/master/engine/interpretation.rkt#L45"]{problem
spot} is very similar to the example from page 1 of the paper. Specifically,
the program branches (the @racket[#:when x] from the link) on a value that is
assumed to be concrete, but supplying a symbolic value causes a different
branch to execute. In this case, the list comprehension does not filter out the
undesired cases.

@subsubsection{Typed}
@EXAMPLE{cats-typed.rkt}

The typed version raises a type error when the unlifted function is given a symbolic argument.

To further explore the typed version of the ocelot library, one can start from
the test suite. To run the typed ocelot test suite (assuming the package is
installed):

@tt{raco test -p ocelot}

@subsection{Synthesizing Incremental Algorithms}

@EXAMPLE{incremental.rkt}

The paper describes two examples. The first requires a symbolic type annotation
in order to successfully mutate a vector in a symbolic path. The second uses
occurrence typing to eliminate a "Maybe"-type-like union.

To further explore the typed incremental language, one can start from the test
suite. Enter the following command to run the test suite:

@tt{raco test -p incremental}
