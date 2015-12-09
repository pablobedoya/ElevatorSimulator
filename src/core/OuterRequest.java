package core;

/**
 * Request an elevator from floor
 */
public class OuterRequest extends Request {
    private /*@ spec_public @*/ int currentFloor; // floor where the button was pressed
    private /*@ spec_public non_null @*/ Human presser; // User who pressed the button

    /*@ requires currentFloor >= 0;
	@	assignable stopFloor;
	@	ensures stopFloor == currentFloor; @*/
    public OuterRequest(){
        stopFloor = currentFloor;
    }

    /*@ requires (dir == Direction.UP || dir == Direction.DOWN);
	  @	assignable direction;
	  @	ensures direction == dir;
	  @	ensures \result == OuterRequest; @*/
    public OuterRequest setDirection(Direction dir) {
        direction = dir;
        return this;
    }

    /*@	requires currentFloor >= 0;
     @ 	ensures \result == currentFloor; @*/
    public /*@ pure @*/ int getCurrentFloor() {
        return currentFloor;
    }

    /*@ requires curFloor >= 0;
	@	assignable currentFloor;
	@	assignable stopFloor;
	@	ensures currentFloor == curFloor;
	@	ensures stopFloor == curFloor;
	@	ensures \result == OuterRequest; @*/
    public OuterRequest setCurrentFloor(int curFloor) {
        currentFloor = curFloor;
        stopFloor = curFloor;
        return this;
    }

    /*@	ensures \result == presser; @*/
    public /*@ pure @*/ Human getPresser() {
        return presser;
    }

    /*@ requires pres != null;
	@	assignable presser;
	@	ensures presser == pres;
	@	ensures \result == OuterRequest; @*/
    public OuterRequest setPresser(Human pres) {
        presser = pres;
        return this;
    }
}