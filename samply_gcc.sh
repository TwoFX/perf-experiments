#!/bin/sh
lake clean
LEAN_CC=gcc lake build -q --log-level=error
samply record ./.lake/build/bin/btree