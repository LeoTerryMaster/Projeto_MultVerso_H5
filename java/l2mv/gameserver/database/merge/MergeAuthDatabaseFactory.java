//package l2mv.gameserver.database.merge;
//
//import java.sql.Connection;
//import java.sql.SQLException;
//
//import l2mv.commons.dbcp.BasicDataSource;
//import l2mv.gameserver.Config;
//import l2mv.gameserver.ConfigHolder;
//
//public class MergeAuthDatabaseFactory extends BasicDataSource
//{
//	public MergeAuthDatabaseFactory()
//	{
//		super(Config.DATABASE_DRIVER, ConfigHolder.getString("MergeAuthUrl"), ConfigHolder.getString("MergeAuthLogin"), ConfigHolder.getString("MergeAuthPassword"), Config.DATABASE_MAX_CONNECTIONS, Config.DATABASE_MAX_CONNECTIONS, Config.DATABASE_MAX_IDLE_TIMEOUT, Config.DATABASE_IDLE_TEST_PERIOD, false);
//	}
//
//	@Override
//	public Connection getConnection() throws SQLException
//	{
//		return getConnection(null);
//	}
//
//	public static MergeAuthDatabaseFactory getInstance()
//	{
//		return SingletonHolder.instance;
//	}
//
//	private static class SingletonHolder
//	{
//		private static final MergeAuthDatabaseFactory instance = new MergeAuthDatabaseFactory();
//	}
//}
