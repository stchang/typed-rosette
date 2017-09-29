#lang scribble/manual

@require[scribble/eval
         scriblib/autobib
         racket/list]

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
  @item{a copy of the POPL 2018 camera-ready @hyperlink[@file://[PAPER]]{[link]},}
  @item{a distribution of the Racket programming language (v6.10.1),}

  @item{and a prototype implementation of the Typed Rosette language and some
        of its libraries.}
  ]

The goals of this artifact are to:
@itemlist[
  @item{provide a tour of the Typed Rosette language via examination of runnable versions of the paper's examples,}
  @item{and review a few of the evaluation examples.}
 ]


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
@section[#:tag "examples"]{Code From the Paper}

For readability and conciseness, the paper occasionally stylizes or elides code
and thus some examples may not run exactly as presented. This artifact, however,
includes and describes runnable versions of all the paper's examples.

The file links in the following subsections open in the browser by default. (If
not viewing in the VM, you may need to adjust your browser's "Text Encoding" to
display Unicode.) To run the files, run with @tt{racket} on the command line,
or open with DrRacket.

@subsection{Paper section 1}

The paper's intro section contains a single example that demonstrates the kind
of unintuitive errors that can occur with lenient
symbolic execution, where symbolic values mix with code that may not recognize
them. Specifically, here is the example in (untyped) Rosette:

@codeblock{
#lang rosette

(define-symbolic x integer?) ; defines symbolic value x

;; ok because Rosette lifts `integer?` to handle symbolic vals
(if (integer? x)
    (add1 x)
    (error "can't add non-int")) ; => symbolic value (+ x 1)

;; import raw Racket's `integer?`, as `unlifted-int?`
(require (only-in racket [integer? unlifted-int?]))

(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int")) ; => error}

This program is also available here: @file-url[POPL-EXAMPLES]{intro-example-untyped-rosette.rkt}

The programmer expects the program to reach the "then" branch and the first
@racket[if] expression does this because Rosette's @racket[integer?] function
recognizes symbolic values.

The second @racket[if] expression, however, reaches the error branch even
though @racket[x] is an integer because the base @racket[integer?] predicate
from @emph{Racket}, which we have renamed to @racket[unlifted-int?], does not
recognize symbolic values.

This kind of error is common in lenient symbolic evaluation, where the
programmer mistakenly allows a symbolic value to reach positions that cannot
handle them. Worse, such an error is difficult to debug and often results the
program silently returning the incorrect value, for example if the "else"
branch above returned a result instead of throwing an error.

Typed Rosette helps lenient symbolic execution by reporting these problems---
when symbolic values flow to positions that do not recognize them---as type
errors:

@codeblock{
#lang typed/rosette

(define-symbolic x integer?) ; defines symbolic value x

;; ok because `integer?` is lifted to handle symbolic vals
(if (integer? x)
    (add1 x)
    (error "can't add non-int")) ; => symbolic value (+ 1 x)

;; import raw Racket's `integer?`, as `unlifted-int?`, with type
(require/type racket [integer? unlifted-int? : (C→ CAny CBool)])

(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int")) ; => type error}

This program is also available in @file-url[POPL-EXAMPLES]{intro-example-typed-rosette.rkt}

In this program, the raw Racket @racket[integer?] is imported with a
@racket[CAny] type, indicating that its input may be any @emph{concrete}
value. Since @racket[x] is a symbolic value, the type checker raises a type error.

@subsection{Paper section 2}

The paper's second section introduces Rosette via examples and further
motivates the need for Typed Rosette.

@subsubsection[#:tag "safe-example"]{Safe Examples}

@file-url[POPL-EXAMPLES]{sec2-rosette-safe-examples.rkt}

The first few examples introduce basic computing with symbolic values in
Rosette and show examples of interacting with the solver, for example to verify
the sortedness of a vector. These examples use the restricted @tt{rosette/safe}
language where all language forms are lifted to recognize symbolic values,
i.e., no lenient symbolic execution is allowed. These "safe" programs aremostly
straightforward so we will not repeat the explanations here.

@subsubsection[#:tag "unsafe-example"]{Unsafe Example}

@file-url[POPL-EXAMPLES]{sec2-rosette-unsafe-hash-example.rkt}

The full @racket[rosette] language supports lenient symbolic execution, i.e.,
programmers may use the full Racket language which includes unlifted constructs
and data structures that are too complicated to encode as solver
constraints. The full Rosette language is unsafe, however, because programmers
must manually concretize symbolic values before they reach unlifted
positions.

This example, similar to the safe vector example from the
@secref{safe-example} section, tries to verify "sortedness" of a hash table,
where the keys are concrete integers acting as the "indices". Even though we
use the same constraints as before, the solver returns a "counterexample" that
supposedly violates our sortedness specification. Inspecting
this "counterexample", however, reveals that it is not actually a
counterexample---it still results in a sorted hash.

At this point, Rosette programmers are often stumped, since the program has
failed silently. In other words, the solver has returned an incorrect result
but the programmer has no information with which to look for the cause of the
problem in the program. Even worse, an inattentive programmer may not think
anything is wrong and instead accept the result of solver as correct. This
highlights the problems with lenient symbolic execution.

@subsubsection{Unsafe Example, with Types}

@file-url[POPL-EXAMPLES]{sec2-typed-rosette-hash-example.rkt}

The problem in the @secref{unsafe-example} is that hash tables are unlifted
; specifically @racket[hash-ref] does not recognize symbolic values but is given
one. Typed Rosette is able to detect this problem and reports it as a type
error, pinpointing the exact source of the problem.


@subsection{Paper section 3}

@subsubsection{Basic Occurrence Typing}

@file-url[POPL-EXAMPLES]{sec31-basic-occurrence-typing.rkt}

These examples demonstrate basic occurrence typing. The input to the @racket[f]
function, @racket[x], may be either a (concrete) integer or string, and the
@racket[integer?] predicate refines @racket[x] to an integer or string in
the "then" and "else" branches, respectively.

The @racket[g] function shows that the predicate's argument may be an arbitrary
expression and is not restricted to plain variables. Nevertheless, @racket[x]'s
type is refined in the same way as in @racket[f].

@subsubsection{Path Concreteness: Motivation}

@file-url[POPL-EXAMPLES]{sec34-path-concreteness1-untyped.rkt}

This example motivates the need for path concreteness when mutation is
involved. Specifically, a concrete value, even if it is only ever mutated with
other concrete values, may change into a symbolic value if mutated under a
symbolic path.

@file-url[POPL-EXAMPLES]{sec34-path-concreteness1-typed.rkt}

Our type system rejects mutation of concrete variables in symbolic paths
because it results in unsoundness. In other words, allowing such mutations
results in variables with concrete types having symbolic values.

@subsubsection{Path Concreteness: Functions}


Functions (that mutate variables) add extra complication since it is the
concreteness of the call sites that we must be concerned about. Typed Rosette
addresses this in two ways.

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
time. But attempting to call this @racket[g] in a symbolic path results in a
type error.}]



@section{Paper Section 5: Typed Rosette Implementation}










@section{}
@subsection{Other files}
@file-url[POPL-EXAMPLES]
@itemlist[@item{@file-url[POPL-EXAMPLES]{abbrv.rkt}: defines abbreviations from
                the paper, like @tt{define-m}.}
          @item{@file-url[POPL-EXAMPLES]{run-all-examples.rkt}: runs all the
                @tt{-prog.rkt} example programs.}]

@; -----------------------------------------------------------------------------
@section{Paper Section 6: MLish}
The paper presents simplistic snippets of the MLish language implementation,
optimized for readability. The actual implementation can be found in the files
listed below.

@file-url[TURNSTILE-EXAMPLES]
@itemlist[@item{@file-url[TURNSTILE-EXAMPLES]{mlish.rkt}: MLish language
                (no type classes).}
          @item{@file-url[TURNSTILE-EXAMPLES]{mlish+adhoc.rkt}: MLish language
                (with type classes); @tt{define-tc} in the paper is
                @tt{define-typeclass}.}]

These implementations fill in the gaps from the paper. The actual
implementations may additionally differ from the paper in other ways, for
example with improved error message reporting and a more efficient type
inference algorithm.

Feel free to experiment with creating your own MLish program. Look at examples
in the @file-url[TURNSTILE-EXAMPLES]{tests/mlish} directory to help get started.

For example, @file-url[MLISH-TEST]{trees.mlish} and
@file-url[MLISH-TEST]{trees-tests.mlish} contain the trees example from the
paper.

@; -----------------------------------------------------------------------------
@section[#:tag "tables"]{Tables From the Paper}

To evaluate Turnstile, we implemented two versions of several example languages:
@itemlist[#:style 'ordered
          @item{a version using Racket, as described in Section 3 of the paper.
                These implementations can be found at:

                @file-url[RACKET-EXAMPLES]}
          @item{a version using Turnstile, as described in Sections 4-6 of the
                paper. These implementations can be found at:

                @file-url[TURNSTILE-EXAMPLES]}]

The languages in each directory extend and reuse components from each other when
possible.

@subsection{Table 1: Summary of reuse (visual)}

Table 1 was compiled using the
@hyperlink[@file://[RACKET-EXAMPLES]]{Racket implementations} (#1 above).
Table 1 remains roughly accurate for the
@hyperlink[@file://[TURNSTILE-EXAMPLES]]{Turnstile versions} (#2), except that
Turnstile defines more things, e.g., @tt{τ=}, automatically.

The (Excel) source for Table 1 is at @file-url[REPO]{extension-table.xlsm}. The
VM does not have a local viewer for the file but the file is viewable with
Google Sheets. It is also publicly downloadable from our repository.

@subsection{Table 2: Summary of reuse (line counts)}

@itemlist[@item{Column 1: reports the exact line numbers of the
@hyperlink[@file://[TURNSTILE-EXAMPLES]]{Turnstile implementations} (#2 above).}

@item{Column 2: estimates the number of lines required to implement
each language without reusing any other languages by adding up the lines for
the relevant languages from column 1. Column 2 is an approximation because it
only counts lines from files that were @emph{entirely} needed to implement the
language in question, and excludes files from which only a few lines are reused.}

@item{Column 3: estimates all the lines of code required by the 
@hyperlink[RACKET-EXAMPLES]{non-Turnstile implementations} (#1 above). Since we
did not explicitly implement every permutation of every language, and instead
followed standard software development practices such as moving common
operations to libraries, column 3 was difficult to compute accurately. To get a
rough idea, we simply added all the lines of code in the language implementations and common library
files together.}]

All line counts include comments and whitespace and all approximate numbers are
rounded to two significant figures. Despite the approximations, this table
remains useful for understanding the degree of reuse achieved by using
Turnstile.

The numbers in Table 2 may be recomputed by running @file-url[REPO]{compute-table2.rkt}.

@subsection{Table 3: Tests (line counts)}

@itemlist[@item{Column 1: number of lines of tests for the core languages, available at:

 @file-url[TURNSTILE-TEST]

Run all (non-MLish) tests by running @file-url[TURNSTILE-TEST]{run-all-tests.rkt}.}

@item{Column 2: number of lines of tests for MLish, available at:

 @file-url[MLISH-TEST]

Run all the MLish tests by running @file-url[TURNSTILE-TEST]{run-all-mlish-tests.rkt}.}]

All line counts include comments and whitespace.

@margin-note{To completely re-compile and re-run all tests (may take ~30-60min):
 @itemlist[@item{@tt{raco setup -c turnstile macrotypes}}
           @item{@tt{raco setup turnstile macrotypes}}
           @item{@tt{raco test turnstile macrotypes}}]}

Particular files of interest for MLish tests:
@itemize[@item{@file-url[MLISH-TEST]{generic.mlish}: example typeclass operations
         }
         @item{@file-url[MLISH-TEST]{term.mlish}: some tests from
          @hyperlink["https://realworldocaml.org/"]{@emph{Real-World OCaml}}
         }
         @item{@file-url[MLISH-TEST]{nbody.mlish},
               @file-url[MLISH-TEST]{fasta.mlish},
               @file-url[MLISH-TEST]{chameneos.mlish}:
          some tests from
          @hyperlink["http://benchmarksgame.alioth.debian.org/"]{The Computer Language Benchmarks Game}
         }
         @item{@file-url[MLISH-TEST]{listpats.mlish},
               @file-url[MLISH-TEST]{match2.mlish}:
          pattern matching tests for lists, tuples, and user-defined datatypes
         }
         @item{@file-url[(build-path MLISH-TEST "bg")]{okasaki.mlish}:
           tests from @emph{Purely Functional Data Structures}
         }
         @item{@file-url[MLISH-TEST]{polyrecur.mlish}: polymorphic, recursive
           type definitions
         }
         @item{@file-url[MLISH-TEST]{queens.mlish},
               @file-url[(build-path MLISH-TEST "bg")]{huffman.mlish}:
          a few other common example programs
         }
]

The numbers in Table 3 may be recomputed by running @file-url[REPO]{compute-table3.rkt}.

@; -----------------------------------------------------------------------------
@section[#:tag "new"]{Building New Typed Languages}

To learn more about @racketmodname[turnstile], view the official 
@racketmodname[turnstile] documentation.

@secref["The_Turnstile_Guide"
         #:doc '(lib "turnstile/scribblings/turnstile.scrbl")]
describes how to build and re-use a new typed language.

@secref["The_Turnstile_Reference"
         #:doc '(lib "turnstile/scribblings/turnstile.scrbl")]
describes all the forms provided
by Turnstile.

