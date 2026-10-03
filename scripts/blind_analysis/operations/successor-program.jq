# NEXT revision of the original declaration-owned programme projection.
# Only the explicit future resource-policy hook differs from the prior owner.
$funding[0] as $original
| $replacement[0] as $new
| $new.retired_members as $retired
| if ($new.members|type)!="array" or ($retired|type)!="array" or ($new.additional_authors|type)!="array"
  then error("missing declared membership") else . end
| if ($new.members|map(.predecessor_slot)|unique|length)!=($new.members|length)
  then error("ambiguous predecessor") else . end
| if ($retired|map(.slot)|unique|length)!=($retired|length)
  then error("ambiguous retirement") else . end
| if any($new.members[]; . as $leaf |
    ([$original.authors[]|select(.slot==$leaf.predecessor_slot)]|length)!=1)
  then error("unknown predecessor") else . end
| if any($retired[]; . as $leaf |
    ([$original.authors[]|select(.slot==$leaf.slot)]|length)!=1)
  then error("unknown retirement") else . end
| if any($retired[]; .slot as $slot | any($new.members[]; .predecessor_slot==$slot))
  then error("replacement also retired") else . end
| .phase = $new.phase
| .funding_root = $new.predecessor_program_root
| .scope_slice = $original.scope_slice
| .state = "prepared_requires_parent_review_and_release"
| .operation_owner_root = $operation_owner_root
| .source_install = $source_install
| .reviewed_source_head = $source_head
| .reviewed_source_merge = $source_head
| .required_skill_merge = $source_head
| .qualification_receipt = $new.package_qualification
| if ($new.resource_policy|type)!="object"
  then error("missing resource policy") else . end
| .proposed_resource_envelope += $original.proposed_resource_envelope + $new.resource_policy
| .authors = $original.authors
| .authors |= map(
    . as $member
    | [$new.members[]|select(.predecessor_slot==$member.slot)] as $leaves
    | if ($leaves|length)==1 then
        .slot = $leaves[0].slot
        | .input_root = $leaves[0].input_root
        | .brief = $leaves[0].brief
        | .scientific_files = $leaves[0].scientific_files
        | .helper_custody.parent_handoff_receipt = $leaves[0].helper_handoff_receipt
        | .writer_handoff = [{program_root:$member.run_owner_root,slot:$member.slot,terminal_custody_receipt:$leaves[0].terminal_custody_receipt}]
        | .run_owner_root = $successor_root
        | .native_thread_id = null
        | .fresh_history = true
      else . end
    | .slot as $slot | select(all($retired[]; .slot!=$slot))
  )
| .authors += $new.additional_authors
| if (.authors|map(.slot)|unique|length)!=(.authors|length)
  then error("ambiguous scientific member") else . end
| if (.authors|map(.display)|unique|length)!=(.authors|length)
  then error("ambiguous physical display") else . end
| [.authors[]|.native_port,.native_ack_port,.viewer_port,.viewer_ack_port,.vnc_port] as $endpoints
| if any($endpoints[]; if type=="number" then .<0 or .>65535 or .!=floor else true end)
  then error("invalid endpoint: expected an integer port, or zero for disabled") else . end
| [$endpoints[]|select(.>0)] as $claimed_endpoints
| if ($claimed_endpoints|unique|length)!=($claimed_endpoints|length)
  then error("ambiguous endpoint") else . end
| .retained_output_roots = (
    [($new.members[]|.predecessor_slot),($retired[]|.slot)] as $terminal |
      $original.retained_output_roots +
      [$terminal[] as $member | $original.authors[] | select(.slot==$member) |
       .run_owner_root+"/"+.slot+"/author-workspace/output"]
    | unique
  )
| .funded_members = [.authors[] | {slot,run_owner_root}]
| .authors |= map(select(.run_owner_root==$successor_root))
