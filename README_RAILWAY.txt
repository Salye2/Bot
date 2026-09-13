V18 RAILWAY CHECKED BUILD

FIXES AFTER V17 AUDIT
- Fixed duplicate payment-check animation.
- Wrong/unverified TX no longer loses the active invoice; customer can paste another TX.
- Added dispatcher-level admin security guard for every adm:* callback.
- Admin callbacks bypass customer force-join gate.
- Webhook success clears stale topup input state.
- Uses Waitress on Railway when installed; Flask dev server remains fallback.
- Supplier API keys are optional at startup, so OWN stock / one supplier can continue if another supplier is disabled.

CORE TESTS PERFORMED
- Python syntax compilation.
- SQLite DB creation/migration.
- Own-stock AVAILABLE -> RESERVED -> DELIVERED flow.
- Quantity purchase and wallet deduction.
- Duplicate delivery protection.
- Top-up idempotency and duplicate TX rejection.
- Supplier ON/OFF persistence.
- Own-stock priority over duplicate supplier listing.
- Invalid TX retry-state behavior.
- Admin callback security gate.

RAILWAY START COMMAND
python ars_bot_multiboard_final_v18_railway_checked.py

PERSISTENT DATABASE
Attach a Railway Volume at:
 /data

Set:
 DB_FILE=/data/ars_bot.db

HEALTHCHECK
/health

WEBHOOK
After Railway generates your public domain:
https://YOUR-DOMAIN.up.railway.app/api/v1/payments/webhook

Use the same PAYMENT_WEBHOOK_SECRET in PayHub.

IMPORTANT
Run ONE replica / ONE bot process only because Telegram getUpdates and SQLite are single-instance here.
