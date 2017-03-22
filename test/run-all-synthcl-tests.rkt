#lang racket/base

(require macrotypes/examples/tests/do-tests)

(do-tests
 "synthcl-tests.rkt"                     "SynthCL general"
 "synthcl-matrix-synth-tests.rkt"        "SynthCL Matrix Mult: synth"
 "synthcl-matrix-verify-tests.rkt"       "SynthCL Matrix Mult: verify"
 "synthcl-matrix-verify-buggy-tests.rkt" "SynthCL buggy Matrix Mult: verify"
 "synthcl-walsh-synth-tests.rkt"         "SynthCL Walsh Transform: synth" 
 "synthcl-walsh-verify-tests.rkt"        "SynthCL Walsh Transform: verify"
 "synthcl-sobel-tests.rkt"        "SynthCL Sobel Filter: synth and verify")
