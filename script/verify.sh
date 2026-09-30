#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/verification
lake build GapFamily BTZEntropy BTZEntropy.Kernel
for audit in Summary GapFamily BTZEntropy; do
    log=".lake/verification/${audit}.log"
    lake env lean "Audit/${audit}.lean" | tee "$log"
    # Fixed counts prevent an accidentally empty or shortened audit from passing.
    case "$audit" in
        Summary) expected=6 ;;
        GapFamily) expected=7 ;;
        BTZEntropy) expected=40 ;;
    esac
    awk -v expected="$expected" '
      /depends on axioms:/ {
        count++; active=1
        sub(/^.*depends on axioms: *\[/, "")
      }
      active {
        done = index($0, "]") > 0
        sub(/\].*$/, "")
        n = split($0, axiom, /[,[:space:]]+/)
        for (i=1; i<=n; i++) {
          a=axiom[i]
          if (a != "" && a != "propext" && a != "Classical.choice" && a != "Quot.sound") {
            print "Unexpected axiom: " a > "/dev/stderr"; bad=1
          }
        }
        if (done) active=0
      }
      /does not depend on any axioms/ { count++ }
      END {
        if (count != expected || active) {
          print "Incomplete axiom audit: " count "/" expected > "/dev/stderr"; bad=1
        }
        exit bad
      }
    ' "$log"
done
printf '%s\n' 'Build and axiom audit passed. Logs: .lake/verification/'
