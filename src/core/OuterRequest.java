package core;

/**
 * 外部电梯请求
 * 每次在电梯外部按下电梯按钮就是一个请求
 */
public class OuterRequest extends Request{
    private int currentFloor; // 按下电梯按钮时的楼层
    private Human presser; // 按按钮的人

    public OuterRequest(){
        stopFloor = currentFloor;
    }

    public OuterRequest setDirection(Direction direction) {
        this.direction = direction;
        return this;
    }

    public int getCurrentFloor() {
        return currentFloor;
    }

    public OuterRequest setCurrentFloor(int currentFloor) {
        this.currentFloor = currentFloor;
        this.stopFloor = currentFloor;
        return this;
    }

    public Human getPresser() {
        return presser;
    }

    public OuterRequest setPresser(Human presser) {
        this.presser = presser;
        return this;
    }
}
