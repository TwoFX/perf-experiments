#!/bin/sh
lake clean
LEAN_CC=clang lake build -q --log-level=error
samply record ./.lake/build/bin/btree