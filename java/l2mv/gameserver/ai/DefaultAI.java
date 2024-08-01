package l2mv.gameserver.ai;

import l2mv.commons.lang.reference.HardReference;
import l2mv.commons.math.random.RndSelector;
import l2mv.commons.threading.RunnableImpl;
import l2mv.commons.util.Rnd;
import l2mv.gameserver.Config;
import l2mv.gameserver.ThreadPoolManager;
import l2mv.gameserver.data.xml.holder.NpcHolder;
import l2mv.gameserver.geodata.GeoEngine;
import l2mv.gameserver.model.AggroList.AggroInfo;
import l2mv.gameserver.model.*;
import l2mv.gameserver.model.entity.SevenSigns;
import l2mv.gameserver.model.instances.MinionInstance;
import l2mv.gameserver.model.instances.MonsterInstance;
import l2mv.gameserver.model.instances.NpcInstance;
import l2mv.gameserver.model.quest.QuestEventType;
import l2mv.gameserver.model.quest.QuestState;
import l2mv.gameserver.network.serverpackets.MagicSkillUse;
import l2mv.gameserver.network.serverpackets.StatusUpdate;
import l2mv.gameserver.stats.Env;
import l2mv.gameserver.stats.Stats;
import l2mv.gameserver.stats.conditions.Condition;
import l2mv.gameserver.taskmanager.AiTaskManager;
import l2mv.gameserver.utils.Location;
import l2mv.gameserver.utils.NpcUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.concurrent.ConcurrentSkipListSet;
import java.util.concurrent.ScheduledFuture;

public class DefaultAI extends CharacterAI
{
	protected static final Logger _log = LoggerFactory.getLogger(DefaultAI.class);
	public static String namechar;

	public enum TaskType
	{
		MOVE, INTERACT, ATTACK, CAST, BUFF
	}

	public static final int TaskDefaultWeight = 10000;

	public static class Task
	{
		public TaskType type;
		public Skill skill;
		public HardReference<? extends Creature> target;
		public Location loc;
		public boolean pathfind;
		public int locationOffset = 0;
		public int weight = TaskDefaultWeight;
		public boolean forceUse = false;
		public boolean dontMove = false;
		public Condition cond = null;
		public Env condEnv = new Env(null, target == null ? null : target.get(), skill);
	}

	public void addTaskCast(Creature target, Skill skill)
	{
		Task task = new Task();
		task.type = TaskType.CAST;
		task.target = target.getRef();
		task.skill = skill;
		_tasks.add(task);
		_def_think = true;
	}

	public void addTaskBuff(Creature target, Skill skill)
	{
		Task task = new Task();
		task.type = TaskType.BUFF;
		task.target = target.getRef();
		task.skill = skill;
		_tasks.add(task);
		_def_think = true;
	}

	public void addTaskAttack(Creature target)
	{
		Task task = new Task();
		task.type = TaskType.ATTACK;
		task.target = target.getRef();
		_tasks.add(task);
		_def_think = true;
	}

	public void addTaskAttack(Creature target, Skill skill, int weight)
	{
		Task task = new Task();
		task.type = skill.isOffensive() ? TaskType.CAST : TaskType.BUFF;
		task.target = target.getRef();
		task.skill = skill;
		task.weight = weight;
		_tasks.add(task);
		_def_think = true;
	}

	public void addTaskMove(Location loc, boolean pathfind)
	{
		Task task = new Task();
		task.type = TaskType.MOVE;
		task.loc = loc;
		task.pathfind = pathfind;
		_tasks.add(task);
		_def_think = true;
	}

	protected void addTaskMove(int locX, int locY, int locZ, boolean pathfind)
	{
		addTaskMove(new Location(locX, locY, locZ), pathfind);
	}

	private static class TaskComparator implements Comparator<Task>
	{
		private static final Comparator<Task> instance = new TaskComparator();

		public static Comparator<Task> getInstance()
		{
			return instance;
		}

		@Override
		public int compare(Task o1, Task o2)
		{
			if ((o1 == null) || (o2 == null))
			{
				return 0;
			}
			return o2.weight - o1.weight;
		}
	}

	protected class Teleport extends RunnableImpl
	{
		Location _destination;

		public Teleport(Location destination)
		{
			_destination = destination;
		}

		@Override
		public void runImpl()
		{
			NpcInstance actor = getActor();
			if (actor != null)
			{
				actor.teleToLocation(_destination);
			}
		}
	}

	protected class RunningTask extends RunnableImpl
	{
		@Override
		public void runImpl()
		{
			NpcInstance actor = getActor();
			if (actor != null)
			{
				actor.setRunning();
			}
			_runningTask = null;
		}
	}

	protected class MadnessTask extends RunnableImpl
	{
		@Override
		public void runImpl()
		{
			NpcInstance actor = getActor();
			if (actor != null)
			{
				actor.stopConfused();
			}
			_madnessTask = null;
		}
	}

	protected static class NearestTargetComparator implements Comparator<Creature>
	{
		private final Creature actor;

		public NearestTargetComparator(Creature actor)
		{
			this.actor = actor;
		}

		@Override
		public int compare(Creature o1, Creature o2)
		{
			// double diff = actor.getDistance3D(o1) - actor.getDistance3D(o2);
			double diff = actor.getDistance3DNoRoot(o1) - actor.getDistance3DNoRoot(o2);
			if (diff < 0.0)
			{
				return -1;
			}
			return diff > 0.0 ? 1 : 0;
		}
	}

	protected long AI_TASK_ATTACK_DELAY = Config.AI_TASK_ATTACK_DELAY;
	protected long AI_TASK_ACTIVE_DELAY = Config.AI_TASK_ACTIVE_DELAY;
	protected long AI_TASK_DELAY_CURRENT = AI_TASK_ACTIVE_DELAY;
	protected int MAX_PURSUE_RANGE;
	protected int MAX_Z_AGGRO_RANGE = 200;

	protected ScheduledFuture<?> _aiTask;
	private long aiTaskDelayCurrent;
	private long lastActiveCheck;

	protected ScheduledFuture<?> _runningTask;
	protected ScheduledFuture<?> _madnessTask;

	/** The flag used to indicate that a thinking action is in progress */
	private boolean _thinking = false;
	/** Показывает, есть ли задания */
	protected boolean _def_think = false;

	/** The L2NpcInstance aggro counter */
	protected long _globalAggro;

	protected long _randomAnimationEnd;
	protected int _pathfindFails;

	/** Список заданий */
	protected final NavigableSet<Task> _tasks = new ConcurrentSkipListSet<>(TaskComparator.getInstance());

	protected Skill[] _damSkills, _dotSkills, _debuffSkills, _healSkills, _buffSkills, _stunSkills;

	protected long _lastActiveCheck;
	protected long _checkAggroTimestamp = 0;
	/** Время актуальности состояния атаки */
	protected long _attackTimeout;

	protected long _lastFactionNotifyTime = 0;
	protected long _minFactionNotifyInterval = 10000;

	protected final Comparator<Creature> _nearestTargetComparator;

	/**
	 * The DefaultAI class is responsible for controlling the behavior of a non-playable character (NPC).
	 * This class extends the AI class and provides default implementation for the AI behavior.
	 */
	public DefaultAI(NpcInstance actor) {
		super(actor);
		setAttackTimeout(Long.MAX_VALUE);
		initializeSkills(actor);
		_nearestTargetComparator = new NearestTargetComparator(actor);
		initializeParameters(actor);
	}

	/**
	 * Initializes the skills of the given NPC.
	 *
	 * @param npc the NPC instance whose skills are to be initialized
	 */
	private void initializeSkills(NpcInstance npc) {
		_damSkills = npc.getTemplate().getDamageSkills();
		_dotSkills = npc.getTemplate().getDotSkills();
		_debuffSkills = npc.getTemplate().getDebuffSkills();
		_buffSkills = npc.getTemplate().getBuffSkills();
		_stunSkills = npc.getTemplate().getStunSkills();
		_healSkills = npc.getTemplate().getHealSkills();
	}

	/**
	 * Initializes parameters for the given NPC actor.
	 *
	 * @param actor the NPC actor to initialize parameters for
	 */
	private void initializeParameters(NpcInstance actor) {
		MAX_PURSUE_RANGE = actor.getParameter(
				"MaxPursueRange",
				actor.isRaid() ? Config.MAX_PURSUE_RANGE_RAID
						: actor.isUnderground() ? Config.MAX_PURSUE_UNDERGROUND_RANGE
						: Config.MAX_PURSUE_RANGE
		);
		_minFactionNotifyInterval = actor.getParameter("FactionNotifyInterval", 10000);
	}

	/**
	 * Method to execute the main logic of the AI task.
	 * Checks if the AI task is valid, if not, the method returns.
	 * If active status needs to be checked, the last active check timestamp is updated and if the actor is not in the active region,
	 * the AI task is stopped and the method returns.
	 * Finally, the onEvtThink method is called to execute the logic for the AI task.
	 */
	@Override
	public void runImpl() {
		if (isAiTaskInvalid()) {
			return;
		}

		if (shouldCheckActiveStatus()) {
			lastActiveCheck = System.currentTimeMillis();
			if (!isActorInActiveRegion()) {
				stopAITask();
				return;
			}
		}
		onEvtThink();
	}

	/**
	 * Checks if the AI task is invalid.
	 *
	 * @return {@code true} if the AI task is invalid, {@code false} otherwise.
	 */
	private boolean isAiTaskInvalid() {
		return _aiTask == null || (!Config.ALLOW_NPC_AIS && (getActor() == null || !getActor().isPlayable()));
	}

	/**
	 * Determines if the active status should be checked.
	 *
	 * @return true if the active status should be checked, false otherwise.
	 */
	private boolean shouldCheckActiveStatus() {
		return !isGlobalAI() && (System.currentTimeMillis() - lastActiveCheck) > 60000L;
	}

	/**
	 * Checks if the actor is in an active region.
	 *
	 * @return {@code true} if the actor is in an active region, {@code false} otherwise.
	 */
	private boolean isActorInActiveRegion() {
		NpcInstance actor = getActor();
		WorldRegion region = (actor == null) ? null : actor.getCurrentRegion();
		return region != null && region.isActive();
	}

	/**
	 * Starts the AI task.
	 *
	 * If the AI task is not already running, this method schedules the task to start after a delay and sets the delay to the default AI task active delay.
	 *
	 * @throws IllegalStateException if the AI task is already running.
	 */
	@Override
	public synchronized void startAITask() {
		if (_aiTask == null) {
			aiTaskDelayCurrent = AI_TASK_ACTIVE_DELAY;
			scheduleAiTask();
		}
	}

	/**
	 * Switches the AI task with a new delay.
	 *
	 * @param newDelay the new delay for the AI task
	 */
	protected synchronized void switchAITask(long newDelay) {
		if (_aiTask != null && aiTaskDelayCurrent != newDelay) {
			_aiTask.cancel(false);
			aiTaskDelayCurrent = newDelay;
			scheduleAiTask();
		}
	}

	/**
	 * Schedules an AI task to be executed periodically.
	 *
	 * This method schedules the execution of an AI task using the AiTaskManager singleton
	 * instance. The task will be executed at a fixed rate, as specified by the aiTaskDelayCurrent
	 * parameter.
	 *
	 * @see AiTaskManager
	 */
	private void scheduleAiTask() {
		_aiTask = AiTaskManager.getInstance().scheduleAtFixedRate(this, 0L, aiTaskDelayCurrent);
	}

	/**
	 * Stops the AI task.
	 *
	 * This method cancels the currently running AI task if it exists. Once the AI task is cancelled, it is set to null.
	 * Subsequent calls to this method will have no effect if there is no AI task currently running.
	 *
	 * Note: This method is thread safe and synchronized to prevent any concurrent modification issues.
	 */
	@Override
	public final synchronized void stopAITask() {
		if (_aiTask != null) {
			_aiTask.cancel(false);
			_aiTask = null;
		}
	}

	/**
	 * Checks if the actor can see the given target in silent move.
	 *
	 * @param target The target Playable object being checked.
	 * @return true if the actor can see the target in silent move, false otherwise.
	 */
	protected boolean canSeeInSilentMove(Playable target) {
		return getActor().getParameter("canSeeInSilentMove", false) || !target.isSilentMoving();
	}

	/**
	 * Determines if the current actor can see the target even if the target is hidden.
	 *
	 * @param target the Playable entity that is being checked for visibility
	 * @return true if the current actor can see the target, false otherwise
	 */
	protected boolean canSeeInHide(Playable target) {
		return getActor().getParameter("canSeeInHide", false) || !target.isInvisible();
	}

	/**
	 * Checks if the given target creature exhibits aggression.
	 *
	 * @param target the creature to check for aggression
	 * @return true if the target creature exhibits aggression, false otherwise
	 */
	protected boolean checkAggression(Creature target) {
		return checkAggression(target, false);
	}

	/**
	 * Checks if the given target can be attacked by the creature.
	 *
	 * @param target the target to check
	 * @param avoidAttack whether to avoid attacking the target or not
	 * @return true if the target can be attacked, false otherwise
	 */
	protected boolean checkAggression(Creature target, boolean avoidAttack) {
		NpcInstance actor = getActor();
		if (isInvalidAggressionTarget(target)) {
			return false;
		}

		if (isTargetProtected(target)) {
			return false;
		}

		if (!isTargetInAggroRange(target)) {
			return false;
		}

		if (!target.isPlayable() || !GeoEngine.canSeeTarget(actor, target, false)) {
			return false;
		}

		if (!avoidAttack) {
			engageTarget(target);
		}

		return true;
	}

	/**
	 * Checks if the given Creature is an invalid aggression target.
	 *
	 * @param target the Creature to check
	 * @return true if the Creature is an invalid aggression target, false otherwise.
	 */
	private boolean isInvalidAggressionTarget(Creature target) {
		return getIntention() != CtrlIntention.AI_INTENTION_ACTIVE || !isGlobalAggro() || target.isAlikeDead();
	}

	/**
	 * Checks if the given target is protected.
	 *
	 * @param target The creature to check.
	 * @return {@code true} if the target is protected, {@code false} otherwise.
	 */
	private boolean isTargetProtected(Creature target) {
		if (target.isNpc() && target.isInvul()) {
			return true;
		}

		if (target.isPlayer() && target.getPlayer().isInAwayingMode() && !Config.AWAY_PLAYER_TAKE_AGGRO) {
			return true;
		}

		if (target.isPlayable()) {
			if (!canSeeInSilentMove((Playable) target) || !canSeeInHide((Playable) target)) {
				return true;
			}
			return isFactionProtected(target);
		}

		return false;
	}

	/**
	 * Checks if a given creature is protected by a faction.
	 *
	 * @param target the creature to be checked for faction protection
	 * @return true if the creature is protected by a faction, false otherwise
	 */
	private boolean isFactionProtected(Creature target) {
		NpcInstance actor = getActor();
		Player player = target.getPlayer();
		if (actor.getFaction().getName().equalsIgnoreCase("varka_silenos_clan") && player.getVarka() > 0) {
			return true;
		}

		if (actor.getFaction().getName().equalsIgnoreCase("ketra_orc_clan") && player.getKetra() > 0) {
			return true;
		}

		return (player.isGM() && target.isInvisible()) || (((Playable) target).getNonAggroTime() > System.currentTimeMillis()) ||
				(!player.isActive() || (actor.isMonster() && target.isInZonePeace()));
	}

	/**
	 * Checks if the target creature falls within the aggro range of the actor.
	 *
	 * @param target the target creature
	 * @return true if the target is within the aggro range, false otherwise
	 */
	private boolean isTargetInAggroRange(Creature target) {
		NpcInstance actor = getActor();
		AggroInfo ai = actor.getAggroList().get(target);

		if (ai != null && ai.hate > 0) {
			return target.isInRangeZ(actor.getSpawnedLoc(), MAX_PURSUE_RANGE);
		}

		return actor.isAggressive() && target.isInRangeZ(actor.getSpawnedLoc(), actor.getAggroRange());
	}

	/**
	 * Engages a target for attack.
	 *
	 * This method is responsible for engaging a target Creature for attack. It adds the target to the actor's aggro list
	 * with an initial hate value of 0 and a weight of 2. If the target is a summon or pet, it also adds the target's player
	 * to the aggro list with an initial hate value of 0 and a weight of 1. It then starts a running task with a delay
	 * specified by the AI_TASK_ATTACK_DELAY constant. Finally, it sets the AI's intention to attack the target.
	 *
	 * @param target the target Creature to engage
	 */
	private void engageTarget(Creature target) {
		NpcInstance actor = getActor();
		actor.getAggroList().addDamageHate(target, 0, 2);

		if (target.isSummon() || target.isPet()) {
			actor.getAggroList().addDamageHate(target.getPlayer(), 0, 1);
		}

		startRunningTask(AI_TASK_ATTACK_DELAY);
		setIntention(CtrlIntention.AI_INTENTION_ATTACK, target);
	}

	/**
	 * Sets the flag indicating if the object is in a random animation.
	 *
	 * @param time the duration of the random animation in milliseconds
	 */
	protected void setIsInRandomAnimation(long time) {
		_randomAnimationEnd = System.currentTimeMillis() + time;
	}

	/**
	 * Generates a random animation for the NPC actor.
	 *
	 * @return true if a random animation is successfully generated, false otherwise.
	 */
	protected boolean randomAnimation() {
		NpcInstance actor = getActor();

		if (actor.getParameter("noRandomAnimation", false)) {
			return false;
		}

		if (actor.hasRandomAnimation() && !actor.isActionsDisabled() && !actor.isMoving() && !actor.isInCombat() && Rnd.chance(Config.RND_ANIMATION_RATE)) {
			setIsInRandomAnimation(3000);
			actor.onRandomAnimation();
			return true;
		}
		return false;
	}

	/**
	 * This method performs a random walk for an NPC.
	 *
	 * @return boolean - Returns true if the random walk was performed successfully, otherwise false.
	 */
	protected boolean randomWalk() {
		NpcInstance actor = getActor();

		if (actor.getParameter("noRandomWalk", false)) {
			return false;
		}

		return !actor.isMoving() && maybeMoveToHome();
	}

	/**
	 * Determines the next action for the active Non-Player Character (NPC).
	 *
	 * @return true if the NPC should continue thinking and performing actions, false otherwise
	 */
	protected boolean thinkActive() {
		NpcInstance actor = getActor();
		if (actor.isActionsDisabled() || (_randomAnimationEnd > System.currentTimeMillis())) {
			return true;
		}

		if (_def_think) {
			if (doTask()) {
				clearTasks();
			}
			return true;
		}

		if (checkAggroConditions(actor)) {
			return true;
		}

		if (actor.isMinion()) {
			return handleMinionMovement(actor);
		}

		return randomAnimation() || randomWalk();
	}

	/**
	 * Checks the aggro conditions for a given NPC instance.
	 *
	 * @param actor the NPC instance to check the aggro conditions for
	 * @return true if the NPC should become aggressive, false otherwise
	 */
	private boolean checkAggroConditions(NpcInstance actor) {
		long now = System.currentTimeMillis();
		if ((now - _checkAggroTimestamp) > Config.AGGRO_CHECK_INTERVAL) {
			_checkAggroTimestamp = now;

			boolean aggressive = Rnd.chance(actor.getParameter("SelfAggressive", actor.isAggressive() ? 100 : 0));
			if (!actor.getAggroList().isEmpty() || aggressive) {
				return evaluateSurroundingsForAggression(actor, aggressive);
			}
		}
		return false;
	}

	/**
	 * Evaluates the surroundings of an NPC to determine if it should exhibit aggression.
	 *
	 * @param actor The NPC instance
	 * @param aggressive Determines if the actor is already aggressive or not
	 * @return true if the NPC should exhibit aggression, false otherwise
	 */
	private boolean evaluateSurroundingsForAggression(NpcInstance actor, boolean aggressive) {
		List<Creature> knowns = World.getAroundCharacters(actor);
		if (!knowns.isEmpty()) {
			List<Creature> aggroList = new ArrayList<>();

			for (Creature cha : knowns) {
				if (aggressive || actor.getAggroList().get(cha) != null) {
					if (checkAggression(cha, true)) {
						aggroList.add(cha);
					}
				}
			}

			if (!aggroList.isEmpty()) {
				Creature target = selectTarget(aggroList);
                return target != null && checkAggression(target, false);
			}
		}
		return false;
	}

	/**
	 * Handles the movement of a minion NPC to its leader.
	 * If the minion has a leader and its distance from the leader exceeds 1000 units,
	 * the minion teleports to the leader's minion position.
	 * If the minion has a leader and its distance from the leader exceeds 200 units
	 * but is below or equal to 1000 units, the minion adds a task to move towards
	 * the leader's minion position.
	 *
	 * @param actor the minion NPC instance
	 * @return true if the minion movement is handled successfully, false otherwise
	 */
	private boolean handleMinionMovement(NpcInstance actor) {
		MonsterInstance leader = ((MinionInstance) actor).getLeader();
		if (leader != null) {
			double distance = actor.getDistance(leader.getX(), leader.getY());
			if (distance > 1000) {
				actor.teleToLocation(leader.getMinionPosition());
			} else if (distance > 200) {
				addTaskMove(leader.getMinionPosition(), false);
			}
			return true;
		}
		return false;
	}

	/**
	 * Evaluates the threat level of a given creature using heuristic.
	 *
	 * @param target the creature to evaluate the threat level for
	 * @return the calculated threat level
	 */
	private double evaluateThreat(Creature target) {
		double threatLevel = 0;
		if (target.isPlayer()) {
			Player player = (Player) target;
			threatLevel += player.getLevel() * 1.5;
			if (player.isGM()) {
				threatLevel += 100;
			}
			if (player.isInParty()) {
				threatLevel += player.getParty().getMemberCount() * 10;
			}
		}
		if (target.isSummon() || target.isPet()) {
			threatLevel += 50;
		}
		return threatLevel;
	}

	/**
	 * Selects a target creature from the provided list based on the threat evaluation heuristic.
	 *
	 * @param aggroList the list of creatures to select a target from
	 * @return the selected target creature or null if the list is empty
	 */
	protected Creature selectTarget(List<Creature> aggroList) {
		return aggroList.stream()
				.max(Comparator.comparingDouble(this::evaluateThreat))
				.orElse(null);
	}

	/**
	 * Checks if the given target is valid for attacking or not.
	 *
	 * @param target The target to be checked.
	 * @param range The maximum range allowed for attacking the target.
	 * @return True if the target is valid for attacking, false otherwise.
	 */
	protected boolean checkTarget(Creature target, int range) {
		NpcInstance actor = getActor();
		if (target == null || target.isAlikeDead() || !actor.isInRangeZ(target, range)) {
			return false;
		}

		// se não podemos ver chars escondidos - não atacamos
		final boolean hidden = target.isPlayable() && !canSeeInHide((Playable) target);

		if (!hidden && actor.isConfused()) {
			return true;
		}

		// Em estado de ataque, atacamos todos com ódio
		if (getIntention() == CtrlIntention.AI_INTENTION_ATTACK) {
			AggroInfo ai = actor.getAggroList().get(target);
			if (ai != null) {
				if (hidden) {
					ai.hate = 0; // limpa o ódio
					return false;
				}
				return ai.hate > 0;
			}
			return false;
		}

		return target.isPlayable();
	}

	/**
	 * Sets the attack timeout for the application.
	 *
	 * @param time the time (in milliseconds) to set as the attack timeout
	 */
	public void setAttackTimeout(long time) {
		_attackTimeout = time;
	}

	/**
	 * Retrieves the attack timeout value.
	 *
	 * @return The attack timeout in milliseconds.
	 */
	protected long getAttackTimeout() {
		return _attackTimeout;
	}

	/**
	 * This method is responsible for determining the actions that an NPC should take when attacking.
	 * It checks if the actor is dead, and if so, returns immediately.
	 *
	 * If the actor is not dead, it then checks if the actor is out of range of its spawned location.
	 * If it is out of range, it teleports the actor back to its spawn location and returns.
	 *
	 * If the actor is within range, it then checks if the current task should be executed and
	 * if the actor is not currently attacking or casting any skills.
	 *
	 * If the current task should be executed and the actor is not attacking or casting, it
	 * then checks if a new task can be created. If a new task cannot be created, it
	 * then checks if the attack timeout has been reached. If the attack timeout has been reached,
	 * it returns the actor back to its home location.
	 */
	protected void thinkAttack() {
		NpcInstance actor = getActor();
		if (actor.isDead()) {
			return;
		}

		Location loc = actor.getSpawnedLoc();
		if (!actor.isInRange(loc, MAX_PURSUE_RANGE)) {
			teleportHome();
			return;
		}

		if (doTask() && !actor.isAttackingNow() && !actor.isCastingNow()) {
			if (!createNewTask()) {
				if (System.currentTimeMillis() > getAttackTimeout()) {
					returnHome();
				}
			}
		}
	}

	/**
	 * Called when the NPC is spawned into the world.
	 * Sets the global aggro time and sets the AI intention to active.
	 */
	@Override
	protected void onEvtSpawn() {
		setGlobalAggro(System.currentTimeMillis() + getActor().getParameter("globalAggro", 10000L));

		setIntention(CtrlIntention.AI_INTENTION_ACTIVE);
	}

	/**
	 * This method is invoked when the object is ready to perform an action.
	 * It calls the onEvtThink() method to trigger the thinking logic.
	 *
	 * @see #onEvtThink()
	 */
	@Override
	protected void onEvtReadyToAct() {
		onEvtThink();
	}

	/**
	 * This method is called when the target has arrived at its destination.
	 * It calls the {@link #onEvtThink()} method.
	 */
	@Override
	protected void onEvtArrivedTarget() {
		onEvtThink();
	}

	/**
	 * This method is called when the NPC arrives at its destination. It invokes the onEvtThink() method.
	 */
	@Override
	protected void onEvtArrived() {
		onEvtThink();
	}

	/**
	 * Tries to move the creature towards the given target.
	 *
	 * @param target The target creature to move towards.
	 * @return True if the creature was able to move towards the target, false otherwise.
	 */
	protected boolean tryMoveToTarget(Creature target) {
		return tryMoveToTarget(target, 0);
	}

	/**
	 * Tries to move the actor to the target within the specified range.
	 * If the actor fails to follow the target, the pathfind fails counter is incremented.
	 * If the pathfind fails counter exceeds the maximum allowed, and the attack timeout
	 * has passed, and the actor is within the maximum pursue range of the target,
	 * the actor will return home if the target is playable and has low aggro.
	 * Otherwise, the actor will try to move towards the target using pathfinding.
	 * If pathfinding fails, the actor will teleport to the target's location if allowed.
	 *
	 * @param target the target to move towards
	 * @param range the maximum range to move towards the target
	 * @return true if the actor successfully moved towards the target, false otherwise
	 */
	protected boolean tryMoveToTarget(Creature target, int range) {
		NpcInstance actor = getActor();

		if (!actor.followToCharacter(target, actor.getPhysicalAttackRange(), true)) {
			_pathfindFails++;
		}

		if (_pathfindFails >= getMaxPathfindFails() && System.currentTimeMillis() > (getAttackTimeout() - getMaxAttackTimeout() + getTeleportTimeout()) && actor.isInRange(target, MAX_PURSUE_RANGE)) {
			_pathfindFails = 0;

			if (target.isPlayable()) {
				AggroInfo hate = actor.getAggroList().get(target);
				if (hate == null || (hate.damage < 100 && hate.hate < 100)) {
					returnHome();
					return false;
				}
			}
			Location loc = GeoEngine.moveCheckForAI(target.getLoc(), actor.getLoc(), actor.getGeoIndex());
			if (!GeoEngine.canMoveToCoord(actor.getX(), actor.getY(), actor.getZ(), loc.x, loc.y, loc.z, actor.getGeoIndex())) {
				loc = target.getLoc();
			}
			if (canTeleWhenCannotSeeTarget()) {
				actor.teleToLocation(loc);
			}
		}

		return true;
	}

	/**
	 * Determines whether telecommunication is possible when the target is not visible.
	 *
	 * @return {@code true} if telecommunication is possible when the target is not visible, {@code false} otherwise.
	 */
	protected boolean canTeleWhenCannotSeeTarget() {
		return true;
	}

	/**
	 * Executes a task for the NPC.
	 *
	 * @param currentTask the task to handle
	 *
	 * @return {@code true} if the task was executed successfully, {@code false} otherwise.
	 */
	protected boolean maybeNextTask(Task currentTask) {
		// Próxima tarefa
		_tasks.remove(currentTask);
		// Se não houver mais tarefas - determine uma nova
        return _tasks.isEmpty();
    }

	/**
	 * Executes a task for the NPC.
	 *
	 * @return {@code true} if the task was executed successfully, {@code false} otherwise.
	 */
	protected boolean doTask() {
		NpcInstance actor = getActor();

		if (!_def_think) {
			return true;
		}

		Task currentTask = _tasks.pollFirst();
		if (currentTask == null) {
			clearTasks();
			return true;
		}

		if (actor.isDead() || actor.isAttackingNow() || actor.isCastingNow()) {
			return false;
		}

        return switch (currentTask.type) {
            case MOVE -> handleMoveTask(currentTask);
            case ATTACK -> handleAttackTask(currentTask);
            case CAST -> handleCastTask(currentTask);
            case BUFF -> handleBuffTask(currentTask);
            default -> false;
        };

    }

	/**
	 * Handles moving the actor to a given task location.
	 *
	 * @param currentTask the task to handle
	 *
	 * @return {@code true} if the actor successfully moves to the task location, {@code false} otherwise
	 */
	private boolean handleMoveTask(Task currentTask) {
		NpcInstance actor = getActor();
		if (actor.isMovementDisabled() || !getIsMobile()) {
			return true;
		}

		if (actor.isInRange(currentTask.loc, 100)) {
			return maybeNextTask(currentTask);
		}

		if (actor.isMoving) {
			return false;
		}

		if (!actor.moveToLocation(currentTask.loc, 0, currentTask.pathfind)) {
			clientStopMoving();
			_pathfindFails = 0;
			actor.teleToLocation(currentTask.loc);
			return maybeNextTask(currentTask);
		}
		return false;
	}

	/**
	 * Handles the attack task for the NPC.
	 *
	 * @param currentTask The current task of the NPC.
	 * @return True if the attack task is complete, false otherwise.
	 */
	private boolean handleAttackTask(Task currentTask) {
		NpcInstance actor = getActor();
		Creature target = currentTask.target.get();

		if (!checkTarget(target, MAX_PURSUE_RANGE)) {
			return true;
		}

		setAttackTarget(target);

		if (actor.isMoving) {
			return Rnd.chance(25);
		}

		if (actor.getRealDistance3D(target) <= actor.getPhysicalAttackRange() + 40 && GeoEngine.canSeeTarget(actor, target, false)) {
			clientStopMoving();
			_pathfindFails = 0;
			setAttackTimeout(getMaxAttackTimeout() + System.currentTimeMillis());
			actor.doAttack(target);
			return maybeNextTask(currentTask);
		}

		if (actor.isMovementDisabled() || !getIsMobile()) {
			return true;
		}

		tryMoveToTarget(target);
		return false;
	}

	/**
	 * Handles casting a task for the NPC actor.
	 *
	 * @param currentTask The task to be cast.
	 * @return True if the task was successfully handled, false otherwise.
	 */
	private boolean handleCastTask(Task currentTask) {
		NpcInstance actor = getActor();
		Creature target = currentTask.target.get();

		if (actor.isMuted(currentTask.skill) || actor.isSkillDisabled(currentTask.skill) || actor.isUnActiveSkill(currentTask.skill.getId())) {
			return true;
		}

		boolean isAoE = currentTask.skill.getTargetType() == Skill.SkillTargetType.TARGET_AURA;
		int castRange = currentTask.skill.getAOECastRange();

		if (!checkTarget(target, MAX_PURSUE_RANGE + castRange)) {
			return true;
		}

		setAttackTarget(target);

		if (actor.getRealDistance3D(target) <= castRange + 60 && GeoEngine.canSeeTarget(actor, target, false)) {
			clientStopMoving();
			_pathfindFails = 0;
			setAttackTimeout(getMaxAttackTimeout() + System.currentTimeMillis());
			actor.doCast(currentTask.skill, isAoE ? actor : target, !target.isPlayable());
			return maybeNextTask(currentTask);
		}

		if (actor.isMoving) {
			return Rnd.chance(10);
		}

		if (actor.isMovementDisabled() || !getIsMobile()) {
			return true;
		}

		tryMoveToTarget(target, castRange);
		return false;
	}

	/**
	 * Handles a buff task for the actor.
	 *
	 * @param currentTask The current task to handle.
	 * @return true if the task was handled successfully, false otherwise.
	 */
	private boolean handleBuffTask(Task currentTask) {
		NpcInstance actor = getActor();
		Creature target = currentTask.target.get();

		if (actor.isMuted(currentTask.skill) || actor.isSkillDisabled(currentTask.skill) || actor.isUnActiveSkill(currentTask.skill.getId())) {
			return true;
		}

		if (target == null || target.isAlikeDead() || !actor.isInRange(target, 2000)) {
			return true;
		}

		boolean isAoE = currentTask.skill.getTargetType() == Skill.SkillTargetType.TARGET_AURA;
		int castRange = currentTask.skill.getAOECastRange();

		if (actor.isMoving) {
			return Rnd.chance(10);
		}

		if (actor.getRealDistance3D(target) <= castRange + 60 && GeoEngine.canSeeTarget(actor, target, false)) {
			clientStopMoving();
			_pathfindFails = 0;
			actor.doCast(currentTask.skill, isAoE ? actor : target, !target.isPlayable());
			return maybeNextTask(currentTask);
		}

		if (actor.isMovementDisabled() || !getIsMobile()) {
			return true;
		}

		tryMoveToTarget(target);
		return false;
	}

	/**
	 * Creates a new task.
	 *
	 * @return {@code true} if the task is successfully created, {@code false} otherwise.
	 */
	protected boolean createNewTask()
	{
		return false;
	}

	/**
	 * Clears all the tasks of the actor and prepares a new task for it.
	 *
	 * @return true if a new task is successfully prepared, false otherwise.
	 */
	protected boolean defaultNewTask() {
		clearTasks();

		NpcInstance actor = getActor();
		Creature target;
		if ((actor == null) || ((target = prepareTarget()) == null)) {
			return false;
		}

		double distance = actor.getDistance(target);
		return chooseTaskAndTargets(null, target, distance);
	}

	/**
	 * Executes the think logic for the AI. This method is called by the AI framework
	 * to determine the next action of the NPC.
	 */
	@Override
	protected void onEvtThink() {
		NpcInstance actor = getActor();
		if (_thinking || actor == null || actor.isActionsDisabled() || actor.isAfraid()) {
			return;
		}

		if (_randomAnimationEnd > System.currentTimeMillis()) {
			return;
		}

		_thinking = true;
		try {
			switch (getIntention()) {
				case AI_INTENTION_ACTIVE:
					if (!Config.BLOCK_ACTIVE_TASKS) {
						thinkActive();
					}
					break;
				case AI_INTENTION_ATTACK:
					thinkAttack();
					break;
				default:
					break;
			}
		} finally {
			_thinking = false;
		}
	}


	/**
	 * This method is called when the Creature associated with this AI instance dies.
	 * It is responsible for handling the logic related to transforming the dead NPC into another NPC, based on certain parameters.
	 *
	 * @param killer the Creature that killed the NPC
	 */
	@Override
	protected void onEvtDead(Creature killer) {
		final NpcInstance actor = getActor();
		final int transformer = actor.getParameter("transformOnDead", 0);
		final int chance = actor.getParameter("transformChance", 100);

		if (transformer > 0 && Rnd.chance(chance)) {
			final NpcInstance npc = NpcUtils.spawnSingle(transformer, actor.getLoc(), actor.getReflection());
			if (killer != null && killer.isPlayable()) {
				npc.getAI().notifyEvent(CtrlEvent.EVT_AGGRESSION, killer, 100);
				killer.setTarget(npc);
				killer.sendPacket(npc.makeStatusUpdate(StatusUpdate.CUR_HP, StatusUpdate.MAX_HP));
			}
		}

		super.onEvtDead(killer);
	}


	/**
	 * This method is called when a clan is attacked.
	 *
	 * @param attacked The creature that is being attacked.
	 * @param attacker The creature that initiated the attack.
	 * @param damage   The amount of damage inflicted.
	 */
	@Override
	protected void onEvtClanAttacked(Creature attacked, Creature attacker, int damage) {
		if ((getIntention() != CtrlIntention.AI_INTENTION_ACTIVE) || !isGlobalAggro()) {
			return;
		}

		NpcInstance actor = getActor();
		if (actor == null || !actor.isInRange(attacked, actor.getFaction().getRange()) || Math.abs(attacker.getZ() - actor.getZ()) > MAX_Z_AGGRO_RANGE) {
			return;
		}

		if (GeoEngine.canSeeTarget(actor, attacked, false)) {
			notifyEvent(CtrlEvent.EVT_AGGRESSION, new Object[]{attacker, attacker.isSummon() ? damage : 2});
		}
	}


	/**
	 * Handles the event when the actor is attacked by a creature.
	 *
	 * @param attacker the creature that is attacking the actor
	 * @param damage the amount of damage inflicted by the attacker
	 */
	@Override
	protected void onEvtAttacked(Creature attacker, int damage) {
		NpcInstance actor = getActor();
		if (attacker == null || actor.isDead()) {
			if (actor.isDead()) {
				notifyFriends(attacker, damage);
			}
			return;
		}

		handleTransformationOnAttack(attacker);

		Player player = attacker.getPlayer();
		if (player != null) {
			handlePlayerAttack(actor, player);
		}

		actor.getAggroList().addDamageHate(attacker, 0, damage);

		if (damage > 0 && (attacker.isSummon() || attacker.isPet())) {
			actor.getAggroList().addDamageHate(attacker.getPlayer(), 0, actor.getParameter("searchingMaster", false) ? damage : 1);
		}

		if (getIntention() != CtrlIntention.AI_INTENTION_ATTACK) {
			if (!actor.isRunning()) {
				startRunningTask(AI_TASK_ATTACK_DELAY);
			}
			setIntention(CtrlIntention.AI_INTENTION_ATTACK, attacker);
		}

		notifyFriends(attacker, damage);
	}

	/**
	 * Handles the transformation on attack by the attacker.
	 *
	 * @param attacker the attacker Creature object
	 */
	private void handleTransformationOnAttack(Creature attacker) {
		NpcInstance actor = getActor();
		int transformer = actor.getParameter("transformOnUnderAttack", 0);
		if (transformer > 0) {
			int chance = actor.getParameter("transformChance", 5);
			if ((chance == 100) || ((((MonsterInstance) actor).getChampion() == 0) && (actor.getCurrentHpPercents() > 50) && Rnd.chance(chance))) {
				transformAndAttack(attacker, transformer);
			}
		}
	}

	/**
	 * Transforms the attacker into a monster and initiates an attack on a creature.
	 *
	 * @param attacker   the creature initiating the attack
	 * @param transformer the id of the monster to transform the attacker into
	 */
	private void transformAndAttack(Creature attacker, int transformer) {
		NpcInstance actor = getActor();
		MonsterInstance npc = (MonsterInstance) NpcHolder.getInstance().getTemplate(transformer).getNewInstance();
		npc.setSpawnedLoc(actor.getLoc());
		npc.setReflection(actor.getReflection());
		npc.setChampion(((MonsterInstance) actor).getChampion());
		npc.setCurrentHpMp(npc.getMaxHp(), npc.getMaxMp(), true);
		npc.spawnMe(npc.getSpawnedLoc());
		npc.getAI().notifyEvent(CtrlEvent.EVT_AGGRESSION, attacker, 100);
		actor.doDie(actor);
		actor.decayMe();
		attacker.setTarget(npc);
		attacker.sendPacket(npc.makeStatusUpdate(StatusUpdate.CUR_HP, StatusUpdate.MAX_HP));
	}

	/**
	 * Handles player attacks on an NPC actor.
	 *
	 * If the player is not signed for winning cabal, the player
	 * will be teleported to the nearest town. Otherwise, this method
	 * notifies all quests associated with the player's attack on the
	 * NPC actor.
	 *
	 * @param actor the NPC being attacked
	 * @param player the player performing the attack
	 */
	private void handlePlayerAttack(NpcInstance actor, Player player) {
		if (shouldTeleportPlayer(player, actor)) {
			player.sendMessage("You have been teleported to the nearest town because you not signed for winning cabal.");
			player.teleToClosestTown();
			return;
		}

		List<QuestState> quests = player.getQuestsForEvent(actor, QuestEventType.ATTACKED_WITH_QUEST);
        for (QuestState qs : quests) {
            qs.getQuest().notifyAttack(actor, qs);
        }
    }

	/**
	 * Determines whether the player should be teleported based on certain conditions.
	 *
	 * @param player the player to be teleported
	 * @param actor the NPC instance
	 * @return true if the player should be teleported, false otherwise
	 */
	private boolean shouldTeleportPlayer(Player player, NpcInstance actor) {
		if ((SevenSigns.getInstance().isSealValidationPeriod() || SevenSigns.getInstance().isCompResultsPeriod()) && actor.isSevenSignsMonster() && Config.RETAIL_SS) {
			int pcabal = SevenSigns.getInstance().getPlayerCabal(player);
			int wcabal = SevenSigns.getInstance().getCabalHighestScore();
			return pcabal != wcabal && wcabal != SevenSigns.CABAL_NULL;
		}
		return false;
	}

	/**
	 * This method handles the event when the actor becomes aggressive towards a creature.
	 *
	 * @param attacker the creature initiating the aggression
	 * @param aggro the aggression level
	 */
	@Override
	protected void onEvtAggression(Creature attacker, int aggro) {
		NpcInstance actor = getActor();
		if (attacker == null || actor.isDead()) {
			return;
		}

		actor.getAggroList().addDamageHate(attacker, 0, aggro);

		if (aggro > 0 && (attacker.isSummon() || attacker.isPet())) {
			actor.getAggroList().addDamageHate(attacker.getPlayer(), 0, actor.getParameter("searchingMaster", false) ? aggro : 1);
		}

		if (getIntention() != CtrlIntention.AI_INTENTION_ATTACK) {
			if (!actor.isRunning()) {
				startRunningTask(AI_TASK_ATTACK_DELAY);
			}
			setIntention(CtrlIntention.AI_INTENTION_ATTACK, attacker);
		}
	}


	/**
	 * Checks if the actor should potentially move to its home location.
	 *
	 * @return true if the actor successfully moved or teleported to its home location, false otherwise
	 */
	protected boolean maybeMoveToHome() {
		NpcInstance actor = getActor();
		if (actor.isDead()) {
			return false;
		}

		boolean randomWalk = actor.hasRandomWalk();
		Location sloc = actor.getSpawnedLoc();

		if (randomWalk && (!Config.RND_WALK || !Rnd.chance(Config.RND_WALK_RATE))) {
			return false;
		}

		boolean isInRange = actor.isInRangeZ(sloc, Config.MAX_DRIFT_RANGE);

		if (!randomWalk && isInRange) {
			return false;
		}

		Location pos = Location.findPointToStay(actor, sloc, 0, Config.MAX_DRIFT_RANGE);

		actor.setWalking();

		if (!actor.moveToLocation(pos.x, pos.y, pos.z, 0, true) && !isInRange) {
			teleportHome();
		}

		return true;
	}


	/**
	 * Returns the player home. This method is protected and does not return any value.
	 * It internally calls the returnHome method with the default teleportation settings.
	 */
	protected void returnHome()
	{
		returnHome(true, Config.ALWAYS_TELEPORT_HOME);
	}

	/**
	 * Teleports the user to their home location.
	 * This method calls the returnHome method with the options to refresh the home location and activate teleportation animation.
	 */
	protected void teleportHome()
	{
		returnHome(true, true);
	}

	/**
	 * Returns the NPC to its home location.
	 *
	 * @param clearAggro whether to clear the NPC's aggression list
	 * @param teleport   whether to teleport the NPC back home or just move it
	 */
	protected void returnHome(boolean clearAggro, boolean teleport) {
		NpcInstance actor = getActor();
		Location sloc = actor.getSpawnedLoc();

		clearTasks();
		actor.stopMove();

		if (clearAggro) {
			actor.getAggroList().clear(true);
		}

		setAttackTimeout(Long.MAX_VALUE);
		setAttackTarget(null);

		changeIntention(CtrlIntention.AI_INTENTION_ACTIVE, null, null);

		if (teleport) {
			actor.broadcastPacketToOthers(new MagicSkillUse(actor, actor, 2036, 1, 500, 0));
			actor.teleToLocation(sloc.x, sloc.y, GeoEngine.getHeight(sloc, actor.getGeoIndex()));
		} else {
			if (!clearAggro) {
				actor.setRunning();
			} else {
				actor.setWalking();
			}

			addTaskMove(sloc, false);
		}
	}

	/**
	 * Prepares the target for the actor by selecting the most appropriate target based on certain conditions.
	 * If the actor is confused, it returns the attack target.
	 * If the actor is under the effect of madness, it selects a random hated creature from the aggro list as the attack target.
	 * If there are no valid targets in the aggro list within the maximum pursue range, it removes them from the aggro list.
	 * Otherwise, it selects the first valid target from the aggro list as the attack target.
	 *
	 * @return The prepared target for the actor, or null if no suitable target found.
	 */
	protected Creature prepareTarget() {
		NpcInstance actor = getActor();

		if (actor.isConfused()) {
			return getAttackTarget();
		}

		if (Rnd.chance(actor.getParameter("isMadness", 0))) {
			Creature randomHated = actor.getAggroList().getRandomHated();
			if (randomHated != null) {
				setAttackTarget(randomHated);
				if (_madnessTask == null && !actor.isConfused()) {
					actor.startConfused();
					_madnessTask = ThreadPoolManager.getInstance().schedule(new MadnessTask(), 10000);
				}
				return randomHated;
			}
		}

		List<Creature> hateList = actor.getAggroList().getHateList();
		for (Creature cha : hateList) {
			if (!checkTarget(cha, MAX_PURSUE_RANGE)) {
				actor.getAggroList().remove(cha, true);
				continue;
			}
			setAttackTarget(cha);
			return cha;
		}

		return null;
	}

	/**
	 * Determines whether the given skill can be used on the target by the actor, based on various conditions.
	 *
	 * @param skill    the skill to be used
	 * @param target   the target creature on which the skill will be used
	 * @param distance the distance between the actor and the target
	 * @return true if the skill can be used, false otherwise
	 */
	protected boolean canUseSkill(Skill skill, Creature target, double distance) {
		NpcInstance actor = getActor();
		if (skill == null || skill.isNotUsedByAI() || (skill.getTargetType() == Skill.SkillTargetType.TARGET_SELF && target != actor)) {
			return false;
		}

		int castRange = skill.getAOECastRange();
		if (castRange <= 200 && distance > 200) {
			return false;
		}

		if (actor.isSkillDisabled(skill) || actor.isMuted(skill) || actor.isUnActiveSkill(skill.getId())) {
			return false;
		}

		double mpConsume2 = skill.getMpConsume2();
		mpConsume2 = skill.isMagic() ? actor.calcStat(Stats.MP_MAGIC_SKILL_CONSUME, mpConsume2, target, skill) : actor.calcStat(Stats.MP_PHYSICAL_SKILL_CONSUME, mpConsume2, target, skill);

        return !(actor.getCurrentMp() < mpConsume2) && target.getEffectList().getEffectsCountForSkill(skill.getId()) == 0;
    }

	/**
	 * Checks if the given skill can be used on the specified target.
	 *
	 * @param sk     the skill to check if it can be used
	 * @param target the target on which the skill will be used
	 * @return true if the skill can be used on the target, false otherwise
	 */
	protected boolean canUseSkill(Skill sk, Creature target) {
		return canUseSkill(sk, target, 0);
	}

	/**
	 * Selects the usable skills based on the target, distance, and array of skills.
	 *
	 * @param target   the target creature
	 * @param distance the distance to the target
	 * @param skills   the array of skills to be evaluated
	 * @return an array of usable skills, or null if there are no usable skills
	 */
	protected Skill[] selectUsableSkills(Creature target, double distance, Skill[] skills) {
		if (skills == null || skills.length == 0 || target == null) {
			return null;
		}

		Skill[] ret = new Skill[skills.length];
		int usable = 0;

		for (Skill skill : skills) {
			if (canUseSkill(skill, target, distance)) {
				ret[usable++] = skill;
			}
		}

		return usable == 0 ? null : Arrays.copyOf(ret, usable);
	}


	/**
	 * Selects the top skill based on damage for an actor targeting a specific creature.
	 *
	 * @param actor the creature performing the skill
	 * @param target the creature being targeted
	 * @param distance the distance between the actor and the target
	 * @param skills an array of skills to choose from
	 * @return the skill with the highest damage relative to the distance
	 */
	protected static Skill selectTopSkillByDamage(Creature actor, Creature target, double distance, Skill[] skills) {
		if (skills == null || skills.length == 0) {
			return null;
		}

		if (skills.length == 1) {
			return skills[0];
		}

		RndSelector<Skill> rnd = new RndSelector<>(skills.length);
		for (Skill skill : skills) {
			double weight = (skill.getSimpleDamage(actor, target) * skill.getAOECastRange()) / distance;
			rnd.add(skill, (int) Math.max(weight, 1.0));
		}
		return rnd.select();
	}

	/**
	 * Selects the top skill to use based on debuffs.
	 *
	 * @param actor   The creature performing the skill.
	 * @param target  The target creature.
	 * @param distance The distance between the actor and the target.
	 * @param skills  The array of skills to choose from.
	 * @return The selected skill, or null if no suitable skill is found.
	 */
	protected static Skill selectTopSkillByDebuff(Creature actor, Creature target, double distance, Skill[] skills) {
		if (skills == null || skills.length == 0) {
			return null;
		}

		if (skills.length == 1) {
			return skills[0];
		}

		RndSelector<Skill> rnd = new RndSelector<>(skills.length);
		for (Skill skill : skills) {
			if (skill.getSameByStackType(target) != null) {
				continue;
			}
			double weight = (100.0 * skill.getAOECastRange()) / distance;
			rnd.add(skill, (int) Math.max(weight, 1.0));
		}
		return rnd.select();
	}

	/**
	 * Selects the top skill by buff from the given array of skills.
	 *
	 * @param target  the target creature
	 * @param skills  the array of skills to select from
	 * @return the top skill with the highest buff power, or null if no skills are provided
	 */
	protected static Skill selectTopSkillByBuff(Creature target, Skill[] skills) {
		if (skills == null || skills.length == 0) {
			return null;
		}

		if (skills.length == 1) {
			return skills[0];
		}

		RndSelector<Skill> rnd = new RndSelector<>(skills.length);
		for (Skill skill : skills) {
			if (skill.getSameByStackType(target) != null) {
				continue;
			}
			double weight = skill.getPower();
			rnd.add(skill, (int) Math.max(weight, 1.0));
		}
		return rnd.select();
	}

	/**
	 * Selects the skill that has the highest healing power based on the difference between the target's maximum HP and its current HP.
	 *
	 * @param target the creature to heal
	 * @param skills the array of skills to choose from
	 * @return the skill with the highest healing power, or null if the skills array is empty, null, or the difference between the target's maximum HP and its current HP is less than
	 *  1.
	 */
	protected static Skill selectTopSkillByHeal(Creature target, Skill[] skills) {
		if (skills == null || skills.length == 0 || target.getMaxHp() - target.getCurrentHp() < 1) {
			return null;
		}

		if (skills.length == 1) {
			return skills[0];
		}

		RndSelector<Skill> rnd = new RndSelector<>(skills.length);
		for (Skill skill : skills) {
			double weight = Math.abs(skill.getPower() - (target.getMaxHp() - target.getCurrentHp()));
			rnd.add(skill, (int) Math.max(weight, 1.0));
		}
		return rnd.select();
	}


	/**
	 * Adds desired skills to the skill map based on the target, distance, and array of skills.
	 *
	 * @param skillMap  the map of skills and their corresponding weights
	 * @param target    the target creature
	 * @param distance  the distance from the target
	 * @param skills    the array of skills to be added
	 */
	protected void addDesiredSkill(Map<Skill, Integer> skillMap, Creature target, double distance, Skill[] skills) {
		if (skills == null || skills.length == 0 || target == null) {
			return;
		}
		for (Skill sk : skills) {
			addDesiredSkill(skillMap, target, distance, sk);
		}
	}

	/**
	 * Adds a desired skill to the skill map based on various conditions.
	 *
	 * @param skillMap the map of skills and their corresponding weights
	 * @param target   the target creature to use the skill on
	 * @param distance the distance between the actor and the target creature
	 * @param skill    the skill to add to the skill map
	 */
	protected void addDesiredSkill(Map<Skill, Integer> skillMap, Creature target, double distance, Skill skill) {
		if (skill == null || target == null || !canUseSkill(skill, target)) {
			return;
		}
		int weight = (int) -Math.abs(skill.getAOECastRange() - distance);
		if (skill.getAOECastRange() >= distance) {
			weight += 1000000;
		} else if (skill.isNotTargetAoE() && skill.getTargets(getActor(), target, false).isEmpty()) {
			return;
		}
		skillMap.put(skill, weight);
	}

	/**
	 * Adds desired skills for healing to the skill map.
	 *
	 * @param skillMap the map that stores the desired skills for healing, where the key is the skill and the value is the weight
	 * @param skills the array of skills to consider for healing
	 */
	protected void addDesiredHeal(Map<Skill, Integer> skillMap, Skill[] skills) {
		if (skills == null || skills.length == 0) {
			return;
		}
		NpcInstance actor = getActor();
		double hpReduced = actor.getMaxHp() - actor.getCurrentHp();
		double hpPercent = actor.getCurrentHpPercents();
		if (hpReduced < 1) {
			return;
		}
		for (Skill sk : skills) {
			if (canUseSkill(sk, actor) && sk.getPower() <= hpReduced) {
				int weight = (int) sk.getPower();
				if (hpPercent < 50) {
					weight += 1000000;
				}
				skillMap.put(sk, weight);
			}
		}
	}

	/**
	 * Adds desired buffs to the given skill map.
	 *
	 * @param skillMap the map containing skills and their respective durations
	 * @param skills the array of skills to be added as desired buffs
	 */
	protected void addDesiredBuff(Map<Skill, Integer> skillMap, Skill[] skills) {
		if (skills == null || skills.length == 0) {
			return;
		}
		NpcInstance actor = getActor();
		for (Skill sk : skills) {
			if (canUseSkill(sk, actor)) {
				skillMap.put(sk, 1000000);
			}
		}
	}

	/**
	 * Selects the top skill from the given skill map based on their weights.
	 *
	 * @param skillMap the map containing skills as keys and their corresponding weights as values
	 * @return the top skill, or null if the skill map is null, empty, or all weights are equal
	 */
	protected Skill selectTopSkill(Map<Skill, Integer> skillMap) {
		if (skillMap == null || skillMap.isEmpty()) {
			return null;
		}
		int topWeight = Integer.MIN_VALUE;
		for (Integer weight : skillMap.values()) {
			if (weight > topWeight) {
				topWeight = weight;
			}
		}
		if (topWeight == Integer.MIN_VALUE) {
			return null;
		}

		List<Skill> topSkills = new ArrayList<>();
		for (Map.Entry<Skill, Integer> entry : skillMap.entrySet()) {
			if (entry.getValue() == topWeight) {
				topSkills.add(entry.getKey());
			}
		}
		return topSkills.isEmpty() ? null : topSkills.get(Rnd.get(topSkills.size()));
	}

	/**
	 * Selects the top skill from the given skill map based on their associated integer values.
	 * If the skill map is empty, null is returned.
	 *
	 * @param skillMap a map where the keys are skill arrays and the values are integers representing their associated values
	 * @return the top skill array or null if the skill map is empty
	 */
	private Skill[] selectTopSkillArray(Map<Skill[], Integer> skillMap) {
		if (skillMap.isEmpty()) {
			return null;
		}
		return skillMap.entrySet().stream()
				.max(Map.Entry.comparingByValue())
				.map(Map.Entry::getKey)
				.orElse(null);
	}


	/**
	 * Chooses a task and targets for the NPC's behavior.
	 *
	 * @param skill the skill to be used by the NPC
	 * @param target the target for the NPC's action
	 * @param distance the distance between the NPC and the target
	 * @return true if a task and targets were successfully chosen, false otherwise
	 */
	protected boolean chooseTaskAndTargets(Skill skill, Creature target, double distance) {
		NpcInstance actor = getActor();

		// Priorizar o uso de habilidades ofensivas se possível
		if (skill != null) {
			target = selectTargetForSkill(skill, distance, target, actor);
			if (target == null) {
				return false;
			}

			if (skill.isOffensive()) {
				addTaskCast(target, skill);
			} else {
				addTaskBuff(target, skill);
			}
			return true;
		}

		// Seleção de habilidade ofensiva com base na distância
		if (actor.isMovementDisabled() && (distance > (actor.getPhysicalAttackRange() + 40))) {
			target = selectTargetForAttack(actor);
		}

		if (target == null) {
			return false;
		}

		addTaskAttack(target);
		return true;
	}

	/**
	 * This method is used to select a target for a given skill.
	 *
	 * @param skill  The skill to use.
	 * @param distance  The distance to the target.
	 * @param target  The current target.
	 * @param actor  The NPC instance using the skill.
	 * @return The selected target for the skill.
	 */
	private Creature selectTargetForSkill(Skill skill, double distance, Creature target, NpcInstance actor) {
		// Verificar se o alvo atual é válido para a habilidade e mudar se necessário
		if (actor.isMovementDisabled() && (distance > (skill.getAOECastRange() + 60))) {
			target = null;
			if (skill.isOffensive()) {
				ArrayList<Creature> potentialTargets = new ArrayList<>();
				for (Creature cha : actor.getAggroList().getHateList()) {
					if (!checkTarget(cha, skill.getAOECastRange() + 60) || !canUseSkill(skill, cha)) {
						continue;
					}
					potentialTargets.add(cha);
				}
				if (!potentialTargets.isEmpty()) {
					target = potentialTargets.get(Rnd.get(potentialTargets.size()));
				}
			}
		}
		return target;
	}

	/**
	 * Selects a target for the attack based on the given actor.
	 *
	 * @param actor The actor (NpcInstance) to select the target for.
	 * @return The selected target (Creature), or null if no valid target is found.
	 */
	private Creature selectTargetForAttack(NpcInstance actor) {
		Creature target = null;
		ArrayList<Creature> potentialTargets = new ArrayList<>();
		for (Creature cha : actor.getAggroList().getHateList()) {
			if (!checkTarget(cha, actor.getPhysicalAttackRange() + 40)) {
				continue;
			}
			potentialTargets.add(cha);
		}
		if (!potentialTargets.isEmpty()) {
			target = potentialTargets.get(Rnd.get(potentialTargets.size()));
		}
		return target;
	}

	@Override
	public boolean isActive()
	{
		return _aiTask != null;
	}

	protected void clearTasks()
	{
		_def_think = false;
		_tasks.clear();
	}


	/**
	 * Starts a running task for the NPC actor with the specified interval.
	 *
	 * @param interval the interval in milliseconds between each execution of the running task
	 */
	protected void startRunningTask(long interval)
	{
		NpcInstance actor = getActor();
		if ((actor != null) && (_runningTask == null) && !actor.isRunning())
		{
			_runningTask = ThreadPoolManager.getInstance().schedule(new RunningTask(), interval);
		}
	}

	protected boolean isGlobalAggro()
	{
		if (_globalAggro == 0)
		{
			return true;
		}
		if (_globalAggro <= System.currentTimeMillis())
		{
			_globalAggro = 0;
			return true;
		}
		return false;
	}

	public void setGlobalAggro(long value)
	{
		_globalAggro = value;
	}

	@Override
	public NpcInstance getActor()
	{
		return (NpcInstance) super.getActor();
	}

	protected boolean defaultThinkBuff(int rateSelf)
	{
		return defaultThinkBuff(rateSelf, 0);
	}

	/**
	 * Notifies the friends of the creature about an attack.
	 *
	 * @param attacker the creature who is attacking
	 * @param damage the amount of damage caused by the attack
	 */
	protected void notifyFriends(Creature attacker, int damage) {
		NpcInstance actor = getActor();
		if ((System.currentTimeMillis() - _lastFactionNotifyTime) <= _minFactionNotifyInterval) {
			return;
		}
		_lastFactionNotifyTime = System.currentTimeMillis();

		if (actor.isMinion()) {
			notifyMasterAndFellowMinions(actor, attacker, damage);
		}

		notifyOwnMinions(actor, attacker, damage);
		notifySocialNpcs(actor, attacker, damage);
	}

	/**
	 * Notifies the master and fellow minions of the given actor about an aggression event.
	 *
	 * @param actor    The actor whose master and fellow minions need to be notified.
	 * @param attacker The creature that initiated the aggression.
	 * @param damage   The amount of damage caused by the aggression.
	 */
	private void notifyMasterAndFellowMinions(NpcInstance actor, Creature attacker, int damage) {
		MonsterInstance master = ((MinionInstance) actor).getLeader();
		if (master != null && !master.isDead() && master.isVisible()) {
			master.getAI().notifyEvent(CtrlEvent.EVT_AGGRESSION, attacker, damage);
			notifyMinions(master, attacker, damage, actor);
		}
	}

	/**
	 * Notifies all alive minions of the given actor about an aggression event.
	 *
	 * @param actor    the NPC instance that owns the minions
	 * @param attacker the creature that initiated the aggression
	 * @param damage   the amount of damage caused by the aggression
	 */
	private void notifyOwnMinions(NpcInstance actor, Creature attacker, int damage) {
		MinionList minionList = actor.getMinionList();
		if (minionList != null && minionList.hasAliveMinions()) {
			for (MinionInstance minion : minionList.getAliveMinions()) {
				minion.getAI().notifyEvent(CtrlEvent.EVT_AGGRESSION, attacker, damage);
			}
		}
	}

	/**
	 * Notifies the social NPCs in the active faction targets list about the attack on the actor.
	 *
	 * @param actor the NPC instance being attacked
	 * @param attacker the creature performing the attack
	 * @param damage the amount of damage caused by the attack
	 */
	private void notifySocialNpcs(NpcInstance actor, Creature attacker, int damage) {
		for (NpcInstance npc : activeFactionTargets(actor)) {
			npc.getAI().notifyEvent(CtrlEvent.EVT_CLAN_ATTACKED, new Object[]{actor, attacker, damage});
		}
	}

	/**
	 * Notifies the minions of a monster instance about an aggression event caused by an attacker.
	 * The method iterates through the alive minions associated with the monster instance, excluding a specified minion,
	 * and notifies their AI about the aggression event, passing the attacker and the damage inflicted.
	 *
	 * @param master    the monster instance whose minions are to be notified
	 * @param attacker  the creature that caused the aggression event
	 * @param damage    the amount of damage inflicted by the attacker
	 * @param exclude   the minion instance to exclude from notification
	 */
	private void notifyMinions(MonsterInstance master, Creature attacker, int damage, NpcInstance exclude) {
		MinionList minionList = master.getMinionList();
		if (minionList != null) {
			for (MinionInstance minion : minionList.getAliveMinions()) {
				if (minion != exclude) {
					minion.getAI().notifyEvent(CtrlEvent.EVT_AGGRESSION, attacker, damage);
				}
			}
		}
	}

	/**
	 * Returns a list of active faction targets for the given NPC actor.
	 *
	 * @param actor the NPC actor for which to find active faction targets
	 * @return a list of NpcInstance objects representing the active faction targets
	 */
	protected List<NpcInstance> activeFactionTargets(NpcInstance actor) {
		if (actor.getFaction().isNone()) {
			return Collections.emptyList();
		}
		List<NpcInstance> npcFriends = new ArrayList<>();
		for (NpcInstance npc : World.getAroundNpc(actor)) {
			if (!npc.isDead() && npc.isInFaction(actor) && npc.isInRangeZ(actor, npc.getFaction().getRange()) && GeoEngine.canSeeTarget(npc, actor, false)) {
				npcFriends.add(npc);
			}
		}
		return npcFriends;
	}

	protected boolean defaultThinkBuff(int rateSelf, int rateFriends) {
		NpcInstance actor = getActor();
		if (actor.isDead()) {
			return true;
		}

		if (Rnd.chance(rateSelf)) {
			return tryToBuffOrHeal(actor);
		}

		if (Rnd.chance(rateFriends)) {
			for (NpcInstance npc : activeFactionTargets(actor)) {
				if (tryToBuffOrHeal(npc)) {
					return true;
				}
			}
		}

		return false;
	}

	private boolean tryToBuffOrHeal(Creature target) {
		double targetHp = target.getCurrentHpPercents();
		Skill[] skills = targetHp < 50 ? selectUsableSkills(target, 0, _healSkills) : selectUsableSkills(target, 0, _buffSkills);
		if (skills == null || skills.length == 0) {
			return false;
		}
		Skill skill = skills[Rnd.get(skills.length)];
		addTaskBuff(target, skill);
		return true;
	}


	protected boolean defaultFightTask() {
		clearTasks();

		NpcInstance actor = getActor();
		if (actor.isDead() || actor.isAMuted()) {
			return false;
		}

		Creature target = prepareTarget();
		if (target == null) {
			return false;
		}

		double distance = actor.getDistance(target);
		double targetHp = target.getCurrentHpPercents();
		double actorHp = actor.getCurrentHpPercents();

		Map<Skill[], Integer> skillMap = new HashMap<>();
		if (actorHp < 50 && Rnd.chance(getRateHEAL())) {
			Skill[] heal = selectUsableSkills(actor, 0, _healSkills);
			skillMap.put(heal, getRateHEAL());
		}
		if (Rnd.chance(getRateBUFF())) {
			Skill[] buff = selectUsableSkills(actor, 0, _buffSkills);
			skillMap.put(buff, getRateBUFF());
		}
		if (Rnd.chance(getRateDAM())) {
			Skill[] dam = selectUsableSkills(target, distance, _damSkills);
			skillMap.put(dam, getRateDAM());
		}
		if (Rnd.chance(getRateDOT())) {
			Skill[] dot = selectUsableSkills(target, distance, _dotSkills);
			skillMap.put(dot, getRateDOT());
		}
		if (targetHp > 10 && Rnd.chance(getRateDEBUFF())) {
			Skill[] debuff = selectUsableSkills(target, distance, _debuffSkills);
			skillMap.put(debuff, getRateDEBUFF());
		}
		if (Rnd.chance(getRateSTUN())) {
			Skill[] stun = selectUsableSkills(target, distance, _stunSkills);
			skillMap.put(stun, getRateSTUN());
		}

		Skill[] selected = selectTopSkillArray(skillMap);
		if (selected != null) {
			if (selected == _damSkills || selected == _dotSkills) {
				return chooseTaskAndTargets(selectTopSkillByDamage(actor, target, distance, selected), target, distance);
			}
			if (selected == _debuffSkills || selected == _stunSkills) {
				return chooseTaskAndTargets(selectTopSkillByDebuff(actor, target, distance, selected), target, distance);
			}
			if (selected == _buffSkills) {
				return chooseTaskAndTargets(selectTopSkillByBuff(actor, selected), actor, distance);
			}
			if (selected == _healSkills) {
				return chooseTaskAndTargets(selectTopSkillByHeal(actor, selected), actor, distance);
			}
		}

		return chooseTaskAndTargets(null, target, distance);
	}

	public int getRatePHYS()
	{
		return 100;
	}

	public int getRateDOT()
	{
		return 0;
	}

	public int getRateDEBUFF()
	{
		return 0;
	}

	public int getRateDAM()
	{
		return 0;
	}

	public int getRateSTUN()
	{
		return 0;
	}

	public int getRateBUFF()
	{
		return 0;
	}

	public int getRateHEAL()
	{
		return 0;
	}

	public boolean getIsMobile()
	{
		return !getActor().getParameter("isImmobilized", false);
	}

	public int getMaxPathfindFails()
	{
		return 3;
	}

	/**
	 * Returns the maximum attack timeout in milliseconds.
	 * The timeout is used to determine the maximum amount of time for an attack to execute.
	 *
	 * @return the maximum attack timeout in milliseconds
	 */
	public int getMaxAttackTimeout()
	{
		return 15000;
	}

	/**
	 * Returns the teleport timeout in milliseconds.
	 *
	 * @return the teleport timeout in milliseconds.
	 */
	public int getTeleportTimeout()
	{
		return 10000;
	}
}