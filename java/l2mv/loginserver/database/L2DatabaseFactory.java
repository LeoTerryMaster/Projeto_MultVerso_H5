package l2mv.loginserver.database;

import java.sql.Connection;
import java.util.logging.Logger;

import org.mariadb.jdbc.MariaDbPoolDataSource;

import l2mv.loginserver.Config;


public class L2DatabaseFactory{
	private static final Logger LOGGER = Logger.getLogger(L2DatabaseFactory.class.getName());

	private static final MariaDbPoolDataSource DATABASE_POOL = new MariaDbPoolDataSource(Config.DATABASE_URL + "&user=" + Config.DATABASE_LOGIN + "&password=" + Config.DATABASE_PASSWORD + "&maxPoolSize=" + Config.DATABASE_MAX_CONNECTIONS);

	public static void init() {
		// Test if connection is valid.
		try {
			DATABASE_POOL.getConnection().close();
			LOGGER.info("Database: Initialized.");
		} catch (final Exception e) {
			LOGGER.info("Database: Problem on initialize. " + e);
		}
	}

	// TODO make it static and drop getInstance()
	public Connection getConnection() {
		Connection con = null;
		while (con == null) {
			try {
				con = DATABASE_POOL.getConnection();
			} catch (final Exception e) {
				LOGGER.severe("DatabaseFactory: Cound not get a connection. " + e);
			}
		}
		return con;
	}

	public void close() {
		try {
			DATABASE_POOL.close();
		} catch (final Exception e) {
			LOGGER.severe("DatabaseFactory: There was a problem closing the data source. " + e);
		}
	}

	/**
	 * @return instance of DatabaseFactory
	 */
	public static L2DatabaseFactory getInstance() {
		return SingletonHolder.INSTANCE;
	}

	private static class SingletonHolder{
		protected static final L2DatabaseFactory INSTANCE = new L2DatabaseFactory();
	}
}
