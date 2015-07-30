#!/bin/sh

#
# How many times have an actor been scheduled on each CPU?
#
/usr/sbin/dtrace -n '

encore$target:::actor_scheduled
{
  @ = quantize(arg3)
}' -c "$*"
