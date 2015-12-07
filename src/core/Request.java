package core;

/**
 * 电梯请求
 */
public class Request {
    protected int stopFloor = 0;
    protected Direction direction;

    public int getStopFloor() {
        return stopFloor;
    }

    public Direction getDirection() {
        return direction;
    }
}
