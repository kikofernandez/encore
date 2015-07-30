#!/bin/sh

sudo dtrace -n 'encore$target:::actor_scheduled { @[arg3, arg2] = count() }' -c "./safe 1000 7 --ponythreads 4"
