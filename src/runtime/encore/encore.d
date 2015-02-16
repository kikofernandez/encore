/*
 * Encore DTrace provider.
 *
 */
provider encore {

  /*
   * Actor create probe.
   * Fires when an actor is created.
   *
   * Emits:
   *   class_name : char *
   *   id         : uint32_t
   *   size       : uint32_t
   */
  probe actor_create(char *class_name, uint32_t id, uint32_t size);
};
