#!/usr/sbin/dtrace -s

*::actor_create {
  printf("%s: id=%d, size=%d\n", copyinstr(arg0), arg1, arg2 );
}
