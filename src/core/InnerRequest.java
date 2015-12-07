package core;

/**
 * 电梯内部请求
 */
public class InnerRequest extends Request{
    private int currentFloor; // 发出请求时电梯所在的楼层
    private int targetFloor; // 要去的楼层
    private Human presser;

    public int getCurrentFloor() {
        return currentFloor;
    }

    public InnerRequest setCurrentFloor(int currentFloor) {
        this.currentFloor = currentFloor;
        setDirection();
        return this;
    }

    public int getTargetFloor() {
        return targetFloor;
    }

    public InnerRequest setTargetFloor(int targetFloor) {
        this.targetFloor = targetFloor;
        this.stopFloor = targetFloor;
        setDirection();
        return this;
    }

    public Human getPresser() {
        return presser;
    }

    public InnerRequest setPresser(Human presser) {
        this.presser = presser;
        return this;
    }

    /**
     * 设置请求的方向
     */
    private void setDirection(){
        if(currentFloor == 0 || targetFloor == 0) return;

        if(currentFloor > targetFloor)
            this.direction = Direction.DOWN;
        else
            this.direction = Direction.UP;
    }
}
