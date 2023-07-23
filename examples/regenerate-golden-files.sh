#!/bin/bash
export KLISTERPATH=`pwd`/examples
cabal run klister-tests -- --accept
