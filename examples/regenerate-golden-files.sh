#!/bin/bash
find . -name '*.golden' | xargs rm
stack test
