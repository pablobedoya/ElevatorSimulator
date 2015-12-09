package core;

/**
 * Request an elevator from inside elevator
 */
public class InnerRequest extends Request {
    private /*@ spec_public @*/ int currentFloor; // elevator current floor
    private /*@ spec_public @*/ int targetFloor; // target floor
    private /*@ spec_public non_null @*/ Human presser; // User who is inside

    /*@	ensures \result == currentFloor; @*/
    public /*@ pure @*/ int getCurrentFloor() {
        return currentFloor;
    }

    /*@	requires curFloor >= 0;
      @	assignable currentFloor;
      @	ensures \result == InnerRequest; @*/
    public InnerRequest setCurrentFloor(int curFloor) {
        currentFloor = curFloor;
        setDirection();
        return this;
    }

    /*@	ensures \result == targetFloor; @*/
    public /*@ pure @*/ int getTargetFloor() {
        return targetFloor;
    }

    /*@	requires tf >= 0;
      @	requires tf != currentFloor;
      @	assignable targetFloor;
      @	assignable stopFloor;
      @	ensures targetFloor == tf;
      @	ensures stopFloor == tf;
      @	ensures \result == InnerRequest; @*/
    public InnerRequest setTargetFloor(int tf) {
        targetFloor = tf;
        stopFloor = tf;
        setDirection();
        return this;
    }

    /*@	ensures \result == presser; @*/
    public /*@ pure @*/ Human getPresser() {
        return presser;
    }

    /*@ requires pres != null;
	  @	assignable presser;
	  @	ensures presser == pres;
	  @	ensures \result == InnerRequest; @*/
    public InnerRequest setPresser(Human pres) {
        presser = pres;
        return this;
    }

    /**
     * set direction request
     */
    /*@ requires currentFloor != 0;
      @ requires targetFloor != 0;
      @ assignable direction;
      @ also
	  @		requires currentFloor > targetFloor;
	  @		ensures direction == Direction.DOWN;
	  @ also
	  @		requires currentFloor < targetFloor;
	  @		ensures direction == Direction.DOWN; @*/
    private void setDirection(){
        if(currentFloor == 0 || targetFloor == 0) return;

        if(currentFloor > targetFloor)
            this.direction = Direction.DOWN;
        else
            this.direction = Direction.UP;
    }
}
