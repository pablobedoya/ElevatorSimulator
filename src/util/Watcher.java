package util;

import core.*;

import java.text.MessageFormat;

/**
 * 系统监视器
 */
public class Watcher{
    public void watch(Elevator elevator){
        // 启动
        elevator.on(ElevatorEvent.LAUNCH, data -> {
            int floor = (Integer)data;
            System.out.println("/\\ "+ floor);
            //Log.info(MessageFormat.format("/\\ {0}", floor));
        });

        // 外部按电梯按钮
        elevator.on(ElevatorEvent.OUTER_PRESSED, data -> {
            OuterRequest req = (OuterRequest)data;
            Human human = req.getPresser();
            String msg = MessageFormat.format("{0} quer {1} do piso {2}",
            		human.getName(), req.getDirection() == Direction.UP ? "subir" : "descer",
            				req.getCurrentFloor());
            //Log.info(msg);
            System.out.println(msg);
        });

        // 内部按电梯按钮
        elevator.on(ElevatorEvent.INNER_PRESSED, data -> {
            InnerRequest req = (InnerRequest)data;
            Human human = req.getPresser();
            String msg = MessageFormat.format("{0} estah indo para o piso {1}",
                    human.getName(), req.getTargetFloor());
            //Log.info(msg);
            System.out.println(msg);
        });

        // 移动
        elevator.on(ElevatorEvent.MOVING, data -> {
            int floor = (Integer)data;
            //Log.info(MessageFormat.format("elevador indo para o piso {0}", floor));
            System.out.println("elevador indo para o piso " + floor);
        });

        // 等待
        elevator.on(ElevatorEvent.PENDING, data -> System.out.println("aguardando"));

        // 开门
        elevator.on(ElevatorEvent.OPEN, data -> {
            int floor = (Integer)data;
            //Log.info(MessageFormat.format("Porta aberta no piso {0}", floor));
            System.out.println("Porta aberta no piso " + floor);
        });

        // 开门
        elevator.on(ElevatorEvent.CLOSE, data -> {
            int floor = (Integer)data;
            //Log.info(MessageFormat.format("Porta fechada no piso {0}", floor));
            System.out.println("Porta fechada no piso " + floor);
        });

        // 进入电梯
        elevator.on(ElevatorEvent.ENTER, data -> {
            Human human = (Human)data;
            //Log.info(MessageFormat.format("{0} entrou no elevador", human.getName()));
            System.out.println(human.getName() + " entrou no elevador");
        });

        // 离开电梯
        elevator.on(ElevatorEvent.LEAVE, data -> {
            Human human = (Human)data;
            //Log.info(MessageFormat.format("{0} saiu do elevador", human.getName()));
            System.out.println(human.getName() + " saiu do elevador");
        });
    }
}
