#!/usr/bin/env nu
# NB: This script expects to be run from the root of the repo

let ls = [s c1 c2 c3 c4]

cabal build clean-room
$ls | par-each {|l| cabal run clean-room -- $l ...$ls }
