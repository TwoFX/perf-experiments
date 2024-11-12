#!/bin/sh
lake clean
LEAN_CC=gcc lake exe --log-level=error btree
