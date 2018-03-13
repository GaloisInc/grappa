#!/bin/sh

# Stupid stack does not seem to respect us telling it below not to build the
# grappa-build project, so we have to ensure that there is a dummy Main.hs file
cp grappa-build/DummyBuildMain.hs grappa-build/Main.hs

stack build grappa:grappa-c
