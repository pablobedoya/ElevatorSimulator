package util;

import java.util.logging.Logger;

/**
 * 全局的log工具
 */
public class Log {
    private static Logger logger = Logger.getLogger("logger");

    public static void info(String msg){
        logger.info(msg);
    }

    public static void error(String msg, Exception e) {
        logger.severe(msg);
        e.printStackTrace();
    }
}
