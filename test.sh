#!/bin/sh
lake clean
LEAN_CC=clang lake exe --log-level=error btree
lake clean
LEAN_CC=gcc lake exe --log-level=error btree
