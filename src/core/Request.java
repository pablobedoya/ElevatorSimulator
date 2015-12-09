package core;

/**
 * Elevator request
 */
public class Request {
	
    protected /*@ spec_public @*/ int stopFloor = 0; //@ in floor;
    protected /*@ spec_public @*/ Direction direction;

    /*@	ensures \result == stopFloor; @*/
    public /*@ pure @*/ int getStopFloor() {
        return stopFloor;
    }

    /*@	requires direction == Direction.UP ||
      @		direction == Direction.DOWN;
      @	ensures \result == direction; @*/
    public /*@ pure @*/ Direction getDirection() {
        return direction;
    }
}
