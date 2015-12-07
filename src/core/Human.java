package core;

import event.EventEmitter;

/**
 * 电梯乘客类
 */
public class Human extends EventEmitter{
    private int currentFloor = 0;
    private int targetFloor = 0;
    private int weight = 0;
    private String name;

    private Elevator elevator;

    public Human(){
        this.on(ElevatorEvent.ENTER, data -> {
            // 在电梯内按下按钮
            elevator.innerPress(targetFloor, this);
        });
    }

    /**
     * 让该乘客在外部按下电梯按钮
     */
    public Human go(){
        elevator.outerPress(currentFloor > targetFloor ? Direction.DOWN : Direction.UP,
                currentFloor, this);
        return this;
    }

    /**
     * 设置乘客对电梯的各种回调操作
     */
    private void setActions(){
        elevator.on(ElevatorEvent.OPEN, data -> {
            int openFloor = (Integer) data;

            // 如果电梯停在了自己的楼层
            if (openFloor == currentFloor) {
                // 进入电梯,触发电梯和自己的进入事件
                elevator.emit(ElevatorEvent.ENTER, this);
                this.emit(ElevatorEvent.ENTER, this);

            } else if (openFloor == targetFloor) {
                // 离开电梯
                elevator.emit(ElevatorEvent.LEAVE, this);
            }
        });
    }

    public int getCurrentFloor() {
        return currentFloor;
    }

    public Human setCurrentFloor(int currentFloor) {
        this.currentFloor = currentFloor;
        return this;
    }

    public int getTargetFloor() {
        return targetFloor;
    }

    public Human setTargetFloor(int targetFloor) {
        this.targetFloor = targetFloor;
        return this;
    }

    public int getWeight() {
        return weight;
    }

    public Human setWeight(int weight) {
        this.weight = weight;
        return this;
    }

    public Elevator getElevator() {
        return elevator;
    }

    public Human setElevator(Elevator elevator) {
        this.elevator = elevator;
        setActions();

        return this;
    }

    public String getName() {
        return name;
    }

    public Human setName(String name) {
        this.name = name;
        return this;
    }
}
