# WTV-MetaRenamer.ps1
#
# Script to scan a folder of WTV files, retrieve the metadata from each file
# and then look on TVDB (and local caches of said data) for matches of
# series name, season number and episode number against that metadata.
#
# If a match is made, the file is renamed and details kept in the undo PS1 file for easy reversal.
#
# Version history:
# 0.00     Initial version
# 0.01     Changed name of config XML file and tweaked text output.
# 0.02     Fixed issue #284 - BestMatchEpisode will pick empty episode names
#          Fixed issue #282 - Proposed improvement to series name matching
#          Fixed issue #285 - Add option to pick single matches
#          Fixed issue #283 - Add interactive mode
#          Fixed issue #337 - BME doesn't work if no valid episode name text can be found
# 0.03     Improved handling if series/episode information isn't cached AND cannot be retrieved from thetvdb
#          Tidied up handling of getting settings from the config file
#          Implemented new functionality to optionally MOVE programmes instead of just renaming them
#		   Move can either be to a single directory or to a series/season structure
#		   Implemented new functionality to perform character remapping
# 0.04     Fixed bug in handling of $move_to; added tests for whether or not it is an array (#479)
# 0.05     Added new functionality:
#            flag to control whether or not the series folder is created if missing
#            flag & code to control if the recording is deleted if the destination file already exists
#            flag & code to control operating on a recording if it is older than the minimum age (#465)
#            flag & code to control ignoring certain series (#416)
# 0.06     Fixed bug in test to check for colon in description. Now looks for colon and a space so that "4:50 From Paddington"
#            doesn't get mis-parsed. Similar change made for ". "
#          Fixed bug in loading of booleans from XML config file
#          Fixed bug in handling of min_age functionality
# 0.07     Fixed bug introduced in the previous change of handling of regex usage.
#          Added a check in RemapFilename to make sure we've actually got some char mappings.
#          Fixed bug in FetchSeriesID so that broadcaster's programme name is saved, not TvDB's.
# 0.08     New functionality to support selecting ONLY specific series (to counter-point ignoring certain series).
#          New functionality to control the output of logging; can now log processing info to a file.
#          New functionality to move unmatched series and episodes to different folders for later examination.
#          New functionality to move duplicates to a different folder for storage in case of errors either in the script
#             or in previous recordings of the same episode.
#          Tweak BME processing so that if the number of changes required is > 50% the length of the string, it is ignored.
# 0.09     Added support for non-English languages.
#          Added configuration item to support different formats of renaming.
#          Added configuration item to move ignored programmes to a folder.
# 0.10     Changed calls to GetDetailsOf to use a function instead so that the textual name of the attribute can be used
#          instead of a fixed index number. Win7 SP1 changed the index numbers!
#          Strange workaround required in GetSeriesID where we now seem to have to force a ToString conversion on a value
#          that is already a string!
# 0.11     Added extra calls to ToString in GetSeriesID (overlooked in v0.10).
# 0.12     Added attributes to config file so that file attribute names can be changed from English easily if required.
#          Now look up attribute indexes once when script runs instead of calling the function introduced in 0.10.
#          Now remap the series name when using it for folder names
#          Added functionality to optionally convert to DVR-MS as part of the renaming process
#
# Original author: Philip Colmer

param([string]$configurationfile, [switch]$interactive)

$VerbosePreference = "SilentlyContinue"
Set-StrictMode –version Latest
$version = "0.12"
$i_am_here = $(Get-Location -PSProvider FileSystem)

# Uses DotNetZip library from CodePlex in order to unpack the series Zip files.
# The DLL is expected to be located in the same folder as this PowerShell script.
Add-Type -Path "$i_am_here\Ionic.Zip.dll"

function get-ld
{
    # get-ld.ps1 (Levenshtein Distance)
    # Levenshtein Distance is the # of edits it takes to get from 1 string to another
    # This is one way of measuring the "similarity" of 2 strings
    # Many useful purposes that can help in determining if 2 strings are similar possibly
    # with different punctuation or misspellings/typos.
    #
    # From https://www.codeproject.com/Tips/102192/Levenshtein-Distance-in-Windows-PowerShell.aspx
    #
    ########################################################

    # Putting this as first non comment or empty line declares the parameters
    # the script accepts
    ###########
    param([string] $first, [string] $second, [switch] $ignoreCase)

    # No NULL check needed, why is that?
    # PowerShell parameter handling converts Nulls into empty strings
    # so we will never get a NULL string but we may get empty strings(length = 0)
    #########################

    $len1 = $first.length
    $len2 = $second.length

    # If either string has length of zero, the # of edits/distance between them
    # is simply the length of the other string
    #######################################
    if($len1 -eq 0)
        { return $len2 }

    if($len2 -eq 0)
        { return $len1 }

    # make everything lowercase if ignoreCase flag is set
    if($ignoreCase -eq $true)
    {
        $first = $first.tolowerinvariant()
        $second = $second.tolowerinvariant()
    }

    # create 2d Array to store the "distances"
    $dist = new-object -type 'int[,]' -arg ($len1+1),($len2+1)

    # initialize the first row and first column which represent the 2
    # strings we're comparing
    for($i = 0; $i -le $len1; $i++) 
        {  $dist[$i,0] = $i }
    for($j = 0; $j -le $len2; $j++) 
        {  $dist[0,$j] = $j }

    $cost = 0

    for($i = 1; $i -le $len1;$i++)
    {
        for($j = 1; $j -le $len2;$j++)
        {
            if($second[$j-1] -ceq $first[$i-1])
            {
                $cost = 0
            }
            else   
            {
                $cost = 1
            }
    
            # The value going into the cell is the min of 3 possibilities:
            # 1. The cell immediately above plus 1
            # 2. The cell immediately to the left plus 1
            # 3. The cell diagonally above and to the left plus the 'cost'
            ##############
            # I had to add lots of parentheses to "help" the Powershell parser
            # And I separated out the tempmin variable for readability
            $tempmin = [System.Math]::Min(([int]$dist[($i-1),$j]+1) , ([int]$dist[$i,($j-1)]+1))
            $dist[$i,$j] = [System.Math]::Min($tempmin, ([int]$dist[($i-1),($j-1)] + $cost))
        }
    }

    # the actual distance is stored in the bottom right cell
    return $dist[$len1, $len2];
}

function Write-VerboseAndLog($str)
{
	Write-Verbose $str
	if ($create_processing_logs)
		{ $str >> $processing_log }
}

function Write-HostAndLog($str)
{
    # Only output to host if running in interactive mode OR
    # we aren't outputting to the log file
    if ($interactive -eq $true -or $create_processing_logs -eq $false)
	    { Write-Host $str}
	if ($create_processing_logs)
		{ $str >> $processing_log }
}

function FetchXml($url)
{
   $result = New-Object XML
   try
   {
      # $result = [xml](New-Object System.Net.WebClient).DownloadString($url)
      $result.Load($url)
   }
   catch
   {
      Write-HostAndLog "... Error! Failed to retrieve $url"
      $result = $null
   }
   Write-Output $result
}

function NodeExists($xmlnode, $to_match)
{
	$this_node = $xmlnode.FirstChild
	do
	{
		if ($this_node.name -eq $to_match)
		{
			return $true
		}
		
		$this_node = $this_node.NextSibling
	} while ($this_node -ne $null)
	
	# Failed to match the node name we are looking for
	Write-Output $false
}

function AllocateDBMirror
{
   $mirrors = FetchXML "http://www.thetvdb.com/api/$apikey/mirrors.xml"
   # $mirrors = New-Object XML; $mirrors.Load("$data_loc\mirrors.xml")
   
   if ($mirrors -ne $null)
   {
       # Find the mirrors that host XML (bit mask 1)
       $xml_mirrors = $mirrors.Mirrors.Mirror | Where-Object { $_.typemask -band 1 }
   
       # Count them so that we can then pick one at random
       $count = 0
       foreach ($mirror in $xml_mirrors) { $count++ }
   
       if ($count -eq 1)
       {
          Write-Output $xml_mirrors.mirrorpath
       }
       else
       {
          $rand = New-Object System.Random
          $this_one = $rand.Next(1,$count+1)
          foreach ($mirror in $xml_mirrors)
          {
             if ($count -eq $this_one) { Write-Output $mirror.mirrorpath; return }
             $count--
          }
       }
   }
   else
   {
       # default to a sensible value
       Write-Output "http://thetvdb.com"
   }
}

function BestMatchEpisode($text)
{
   # This function is called when we have a string to try to match against the episode
   # names but the string isn't matching 100% accurately. For each episode, we calculate
   # the edit distance and use that as an "accuracy" score. After we've performed all
   # of the tests, we'll check the overall accuracy scores to see if there is one we are
   # happy with.
   #
   # Note that if $interactive is true, we output $text to Host rather than Verbose so that if we don't get a match,
   # the user has some context to help them pick matches against
   if ($interactive)
   {
       Write-Host "... BestMatchEpisode called for '$text'"
   }
   else
   {
       Write-VerboseAndLog "... BestMatchEpisode called for '$text'"
   }
   
	# If the text we are being asked to test against is more than twice the length of
	# the longest episode name we have, this probably isn't valid text. For example, it
	# could be the episode synopsis.
	#
	# Retrieve the previously calculated longest episode name - it is stored
	# in the SERIES ID attribute, not the Episode ID (which is used for the scoring)
	$longest_episode_name = $episodes.Data.Series.GetAttribute("ID")
	if ($text.Length -gt (2 * $longest_episode_name))
		{ Write-VerboseAndLog "... BestMatchEpisode: ignoring very long text to test against"; return }
   
	# We also won't bother if we haven't been passed anything!
	if ($text.Length -eq 0)
   		{ Write-VerboseAndLog "... BestMatchEpisode: ignoring empty text to test against"; return }
   
   foreach ($episode in $episodes.Data.Episode)
   {
      # Calculate how many characters would need to be changed in order to match the episode name
      $score = Get-Ld $($episode.EpisodeName) $text -i
      # 0.08: if the score is greater than 50% of the length of $text, we are going to ignore it
      if ($score -gt ($text.Length / 2))
      {
         Write-VerboseAndLog "... '$($episode.EpisodeName)': ignoring score of $score as it exceeds the 50% threshold"
         $score = -1
      }
      elseif (($score -lt $episode.GetAttribute("ID")) -or (-1 -eq $episode.GetAttribute("ID")))
      {
         Write-VerboseAndLog "... '$($episode.EpisodeName)': replacing previous score of $($episode.GetAttribute("ID")) with $score"
         $episode.SetAttribute("ID", $score)
      }
      else
      {
         Write-VerboseAndLog "... '$($episode.EpisodeName)': ignoring score of $score as this is larger than previous score of $($episode.GetAttribute("ID"))"
      }
   }
}

function GetInputFromUser($upper)
{
    # Get input from the user and validate it as either an empty string
    # or a number in the range 1 to $upper.
    # If an empty string, return -1.
    $answer = 0
    do
    {
        $val = Read-Host
        if ($val -ne "")
        {
            $intval = 0
            if ([int]::TryParse($val, [ref]$intval))
            {
                if ($intval -ge 1 -and $intval -le $upper)
                    { $answer = $intval }
            }
        }
        else
            { $answer = -1 }
    } while ( $answer -eq 0 )
    return $answer
}

function MatchEpisode($text)
{
   # Looks through the XML data that has been preloaded into $episodes
   # to see if there is an episode that has an episode name matching the passed text
   # Either returns the season and episode numbers if a match found, or -1 if more
   # than one match found, or 0 if no match found.
   Write-VerboseAndLog "... trying to find an episode that matches '$text'"
   $match = $episodes.Data.Episode | Where-Object { $_.EpisodeName -eq $text }
   if ($match -ne $null)
   {
      # Matched - but how many times?
      $count = 0
      foreach ($ep in $match) { $count++ }
      if ($count -eq 1)
      {
         if ($match.EpisodeNumber -ne 0)
         {
            Write-Output ([int]$match.SeasonNumber)
            Write-Output ([int]$match.EpisodeNumber)
         }
         else
         {
            # An episode number of 0 isn't valid
            Write-VerboseAndLog "... matched but invalid episode number"
            Write-Output ([int]0)
            Write-Output ([int]0)
         }
      }
      else
      {
         Write-HostAndLog "... matched $count times - unable to safely rename"
         $index = 1
         foreach ($ep in $match)
         {
            $s = $([int]$ep.SeasonNumber).ToString("0#")
            $e = $([int]$ep.EpisodeNumber).ToString("0#")
            if ($interactive)
            {
                Write-Host "... [$index] S$($s)E$($e) - $($ep.EpisodeName)"
            }
            else
            {
                Write-HostAndLog "... S$($s)E$($e) - $($ep.EpisodeName)"
            }
            $index++
         }
         
         # We end up with index being one too high ...
         $index--
         
         if ($interactive)
         {
            Write-Host "... Enter a number from 1 to $index or RETURN to skip"
            $answer = GetInputFromUser $index
            if ($answer -ne -1)
            {
                # User provided an answer in the correct range so find it and return
                # that to the function caller
                $index = 1
                foreach ($ep in $match)
                {
                    if ($index -eq $answer)
                    {
                        Write-Output ([int]$ep.SeasonNumber)
                        Write-Output ([int]$ep.EpisodeNumber)
                        return
                    }
                    $index++
                }
            }
         }
         Write-Output ([int]-1)
         Write-Output ([int]-1)
      }
   }
   else
   {
      # Not matched - return zeroes
      Write-VerboseAndLog "... didn't match text"
      Write-Output ([int]0)
      Write-Output ([int]0)
   }
}

function FetchEpisodeInfo($series_info)
{
	$this_series_id = $series_info[0]
	$this_series_lang = $series_info[1]
    # Have we already got the episode information for this series? If we
    # have, load it and return.
    $episode_info = New-Object XML
    try
    {
        $episode_info.Load("$data_loc\EpInfo\$this_series_id.xml")
        Write-VerboseAndLog "... retrieved episode information from cache"
    }

    catch
    {
        # Write-VerboseAndLog "... got error $Error[0] while trying to retrieve ep info from cache"
        
        # We got an error, so let's request the base information, extract
        # the en.xml file and save it as the info for this series.
        
        # But let's also cope with the possibility that we can't retrieve the XML data from the server either!
        trap {
            Write-HostAndLog "... got error while trying to retrieve episode information from server"
            Write-HostAndLog "... $($_.Exception.Message)"
            return $null
        }        
        
        $url = "$tvdb_mirror/api/$apikey/series/$this_series_id/all/$this_series_lang.zip"
        $req = [System.Net.HttpWebRequest]::Create($url)
        $res = $req.GetResponse()
        if ($res.StatusCode -eq 200)
        {
            $reader = $res.GetResponseStream()
            $writer = New-Object System.IO.FileStream "$data_loc\EpInfo\Tmp.zip", "Create"
            [byte[]]$buffer = New-Object byte[] 4096
            do
            {
                $count = $reader.Read($buffer, 0, $buffer.Length)
                $writer.Write($buffer, 0, $count)
            } while ($count -gt 0)
            $reader.Close()
            $writer.Flush()
            $writer.Close()
            $res.Close()
      
            # Now extract "<language>.xml" from the Zip file
            $zip = New-Object Ionic.Zip.ZipFile("$data_loc\EpInfo\Tmp.zip")
            $zip_item = $zip["$this_series_lang.xml"]
            $zip_item.Extract("$data_loc\EpInfo")
            $zip.Dispose()
      
            # Delete the zip file and rename the XML file
            Remove-Item "$data_loc\EpInfo\Tmp.zip"
            Rename-Item "$data_loc\EpInfo\$this_series_lang.xml" "$this_series_id.xml"
            $episode_info.Load("$data_loc\EpInfo\$this_series_id.xml")
            Write-VerboseAndLog "... downloaded episode information from server"
        }
        else
        {
            Write-VerboseAndLog "... failed to retrieve episode information from server"
            return $null
        }
    }
    
    # Pre-set the edit distance scores to be -1.
    # The value is stored as an attribute of the ID node as an easy way to stash it.
    # Also track the length of the longest episode name so that we can try to be
    # smarter about when we use best match calculations if the test text is way too long.
    $longest_episode_name = 0
    foreach ($episode in $episode_info.Data.Episode)
    {
        $this_ep_length = $($episode.EpisodeName).Length
        $episode.SetAttribute("ID", -1)
        if ($this_ep_length -gt $longest_episode_name)
            { $longest_episode_name = $this_ep_length }
    }
    # Store the longest length in the *SERIES* ID attribute
    $episode_info.Data.Series.SetAttribute("ID", $longest_episode_name)

    # Return the XML data
    Write-Output $episode_info
}

function FetchSeriesID($series_name)
{
	# Make sure we have been given a series name!
	if ($series_name -eq "")
	{
		Write-HostAndLog "... no series name provided"
		return $null
	}

	# Check to see if the series name has been entered into the cached series database
	$series_list = New-Object XML
	$series_list.Load("$data_loc\SeriesList.xml")
	$this_series = $series_list.Data.Series | Where-Object { $_.SeriesName -eq $series_name }
   
	if ($this_series -ne $null)
	{
		# Got a match - return the series ID
		Write-VerboseAndLog "... FetchSeriesID returning $($this_series.seriesid) from cache"
		Write-Output $this_series.seriesid
		# If this entry in the cache specifies a language code, return that, otherwise
		# return the default language code.
		if (NodeExists $this_series "language")
		{
			Write-VerboseAndLog "... returning language code $($this_series.language)"
			Write-Output $this_series.language
		}
		else
		{
			Write-VerboseAndLog "... returning default language code $default_language"
			Write-Output $default_language
		}
		return
	}

	# If it hasn't, try to retrieve the series ID from TvDB. If only one series is returned
	# we'll go with that. If more than one, list them out for the user to manually update
	# the file and then bork.
	$series_info = FetchXML "$tvdb_mirror/api/GetSeries.php?seriesname='$series_name'"
	if (($series_info -ne $null) -and ($series_info.data -ne ""))
	{
		$count = 0
		foreach ($this_series in $series_info.Data.Series) { $count++ }
      
		if ($count -gt 1)
		{
			# More than one match returned from TvDB - but does one of them match completely?
			Write-VerboseAndLog "... TvDB has returned multiple matches"
         
			foreach ($this_series in $series_info.Data.Series)
			{
				if ($this_series.SeriesName -eq $series_name)
				{
					Write-VerboseAndLog "... got precise match"
					# Add the series information automatically to the list file
					$series_xml = @($series_list.Data.Series)[0]
					$new_series_xml = $series_xml.Clone()
					$new_series_xml.seriesid = $this_series.seriesid
					# Changed to save *broadcaster's* series name, not TvDB's
					$new_series_xml.SeriesName = $series_name.ToString() # $this_series.SeriesName
					$rubbish_output = $series_list.Data.AppendChild($new_series_xml)
					$series_list.Save("$data_loc\SeriesList.xml")

					Write-VerboseAndLog "... returning $($this_series.seriesid) and language $default_language"
					Write-Output $this_series.seriesid
					Write-Output $default_language
					return
				}
			}
		}
   
		if ($count -eq 1)
		{
			Write-VerboseAndLog "... FetchSeriesID has retrieved one match from TvDB"
            Write-VerboseAndLog "... cloning XML entry for '$series_name'"
			# Add the series information automatically to the list file
			$series_xml = @($series_list.Data.Series)[0]
			$new_series_xml = $series_xml.Clone()
			$new_series_xml.seriesid = $series_info.Data.Series.seriesid
			# Changed to save *broadcaster's* series name, not TvDB's
            # Not sure what has broken PowerShell here but we seem to have to force a conversion
            # of a string to a string!
			$new_series_xml.SeriesName = $series_name.ToString() # $series_info.Data.Series.SeriesName
			$rubbish_output = $series_list.Data.AppendChild($new_series_xml)
			$series_list.Save("$data_loc\SeriesList.xml")

			Write-VerboseAndLog "... returning $($series_info.Data.Series.seriesid) and language $default_language"
			Write-Output $series_info.Data.Series.seriesid
			Write-Output $default_language
		}
		else
		{
			if ($interactive)
			{
				Write-Host "More than one series matches series name '$series_name':"
			}
			else
			{
        		Write-HostAndLog "More than one series matches series name '$series_name':"
			}
			$index = 1
			foreach ($this_series in $series_info.Data.Series)
			{
				if ($interactive)
				{
					Write-Host "... [$index] $($this_series.SeriesName)"
				}
				else
				{
					Write-HostAndLog "ID: $($this_series.seriesid); Name: $($this_series.SeriesName)"
				}
				$index++
			}
         
			# We end up with index being one too high ...
			$index--
	         
			if ($interactive)
			{
				Write-Host "... Enter a number from 1 to $index or RETURN to skip"
				$answer = GetInputFromUser $index
				if ($answer -ne -1)
				{
					# User provided an answer in the correct range so find it and return
					# that to the function caller
					$index = 1
					foreach ($this_series in $series_info.Data.Series)
					{
						if ($index -eq $answer)
						{
							# Add the series information automatically to the list file
	                        # N.B. Because there were multiple matches for the series name
	                        # provided, and the user has made their choice, we are going to
	                        # record the pairing of the series name PROVIDED and the matching
	                        # series ID. We DON'T record the *actual* series name otherwise
	                        # it won't match next time either!
							
							Write-VerboseAndLog "... series ID selected as $($this_series.seriesid)"
							
	                        $series_xml = @($series_list.Data.Series)[0]
	                        $new_series_xml = $series_xml.Clone()
	                        $new_series_xml.seriesid = $this_series.seriesid
	                        $new_series_xml.SeriesName = $series_name.ToString()
	                        $rubbish_output = $series_list.Data.AppendChild($new_series_xml)
	                        $series_list.Save("$data_loc\SeriesList.xml")

	                        Write-Output $this_series.seriesid
							Write-Output $default_language
	                        return
	                    }
	                    $index++
					}
				}
			}
         
			return $null
		}
	}
	else
	{
		Write-VerboseAndLog "... failed to retrieve series information from TvDB"
		return $null
	}
}

function SafeBooleanConvert([string]$value)
{
   if (($value -eq '$true') -or ($value -eq "true") -or ($value -eq "1") -or ($value -eq "yes") -or ($value -eq "y"))
      { return $true }
      
   if (($value -eq '$false') -or ($value -eq "false") -or ($value -eq "0") -or ($value -eq "no") -or ($value -eq "n") -or ($value -eq ""))
      { return $false }
      
   throw "Cannot convert '$value' to boolean"
   return $null
}

function CheckForUpdatesSinceLastRun()
{
	# See if we've been run before (i.e. we preserved the TvDB server time)
	try
	{
	   $previous_time = New-Object XML
	   $previous_time.Load("$data_loc\updates.xml")
	}

	catch
	{
	   $previous_time = $null
	}

	# Get the current server time and save it away. We do this before anything
	# else as we always want to do this, even if this is the first run.
	$server_time = FetchXml "http://www.thetvdb.com/api/Updates.php?type=none"
	if ($server_time -ne $null)
	   { $server_time.Save("$data_loc\updates.xml") }

	# If we have a previous time, see which series have been updated since
	# last time. For any series that we have been caching, delete the episode
	# cache. This will cause the script to re-download the episode list if
	# we need to.
	if ($previous_time -ne $null)
	{
	    $time = $previous_time.items.time
	    $changes = FetchXML "http://www.thetvdb.com/api/Updates.php?type=all&time=$time"
	    if ($changes -ne $null)
	    {
			if (NodeExists $changes.items "series")
			{
		        foreach ($s in $changes.items.series)
		        {
		            if (Test-Path "$data_loc\EpInfo\$s.xml")
		            {
		                Write-VerboseAndLog "... series $s has been changed"
		                Remove-Item "$data_loc\EpInfo\$s.xml"
		            }
		        }
			}
            else
            {
                Write-Host "No series updates"
            }
	    }
	}
}

function RemapFilename($name)
{
	$new_name = $name
    if ($char_map -ne $null)
    {
    	foreach ($cm in $char_map)
	    {
		    # convert the "from" string to an array so that we can check for one char at a time
		    $cma = $($cm.from).ToCharArray()
		    # then step through each character, trying to replace any occurences with the "to" string
		    foreach ($c in $cma)
		    {
			    $new_name = $new_name.Replace([string]$c, $cm.to)
		    }
	    }
    }
    
    Write-Output $new_name
}

function SeriesIsInIgnoreList($series_ID)
{
	Write-VerboseAndLog "... SeriesIsInIgnoreList"
	$result = $false
	
	if ($ignore_series -eq $null)
	{
		Write-VerboseAndLog "...... ignore list is empty"
	}
	else
	{
		foreach ($s in $ignore_series)
		{
			if ($s -eq $series_ID)
			{
                Write-HostAndLog "... recording is from a series on the ignore list; skipping"
				$result = $true
			}
		}
	}
	
	Write-VerboseAndLog "...... returning $result"
	return $result
}

function SeriesIsNotInOnlyList($series_ID)
{
	Write-VerboseAndLog "... SeriesIsNotInOnlyList"
	$result = $false
	
	if ($only_series -eq $null)
	{
		Write-VerboseAndLog "...... only list is empty"
	}
	else
	{
		$notfound = $true
		foreach ($s in $only_series)
		{
			if ($s -eq $series_ID)
			{
				$notfound = $false
			}
		}
		if ($notfound)
		{
			Write-HostAndLog "... recording is from a series that is not on the only list; skipping"
		}
		else
		{
			Write-VerboseAndLog "...... matched $series_ID"
		}
		$result = $notfound
	}
	
	Write-VerboseAndLog "...... returning $result"
	return $result
}

# No longer needed as of v0.12. Do the lookup once and store in variables
#function GetFileAttribute($folder, $file, $attr_name)
#{
#    Write-VerboseAndLog "GetFileAttribute $attr_name"
#    foreach ($index in 0..300)
#    {
#        if ($($folder.GetDetailsOf($null, $index)) -eq $attr_name)
#        {
#            Write-VerboseAndLog "... found at index $index"
#            Write-VerboseAndLog "... returning $($folder.GetDetailsOf($file, $index))"
#            return $($folder.GetDetailsOf($file, $index))
#        }
#    }
#
#    Write-HostAndLog "... cannot match $attr_name as an attribute for $file"
#    break
#}

######
###
### Functions to read from the XML config file.
### Note that the Write-XXX calls cannot be to the log file as the XML config file specifies whether or not we want a log file!
###
######

function LoadConfigFile()
{
   # If a configuration filename wasn't specified as a parameter, provide a default
   if ($configurationfile -eq "")
   {
      Write-Host "No configuration file specified; defaulting to $i_am_here\WTV-MetaRenamer.xml"
      $configurationfile = "$i_am_here\WTV-MetaRenamer.xml"
   }
   
   try {
      $foo = New-Object XML
      $foo.Load($configurationfile)
      Write-Output $foo
   }
   
   catch {
      Write-Verbose "... error while loading config file: $($_.Exception.Message)"
      Write-Output $null
   }
}

function GetDefaultLanguage()
{
	# The default language is "en" (English) - we'll use this if nothing else is specified.
	$result = "en"

	try {
		# Only override the default value if a value has actually been provided!
		if ($my_config.config.default_language -ne "")
			{ $result = $my_config.config.default_language }
	}
   
	catch {
		Write-Verbose "... error while retrieving default_language element: $($_.Exception.Message)"
	}  
   
	Write-Output $result
}

function GetXMLCachePath()
{
   # Define the default result
   # Default location where the script is caching data
   $result = "$i_am_here\XML"
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.xml_cache -ne "")
         { $result = $my_config.config.xml_cache }
   }
   
   catch {
      Write-Verbose "... error while retrieving xml_cache element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetRecordingsPath()
{
   # Define the default result
   # Default location where the script should be looking for recordings - the same directory as where the script is running from
   $result = "$i_am_here"
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.recordings -ne "")
         { $result = $my_config.config.recordings }
   }
   
   catch {
      Write-Verbose "... error while retrieving recordings element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetAcceptSingleBME()
{
   # Define the default result
   # By default, we will NOT accept single Best Match Episode results
   $result = $false
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.accept_single_bme -ne "")
         { $result = SafeBooleanConvert $my_config.config.accept_single_bme }
   }
   
   catch {
      Write-Verbose "... error while retrieving accept_single_bme element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetMoveTo()
{
   # Define the default result
   # By default, we will NOT move files, just rename them
   $result = $null

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.move_to -ne "")
         { $result = $my_config.config.move_to }
   }
   
   catch {
      Write-Verbose "... error while retrieving move_to element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetMoveToSingleFolder()
{
   # Define the default result
   # By default, we will NOT be moving files into a single folder, i.e. we
   # will be moving to a series/season structure
   $result = $false
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.move_to_single_folder -ne "")
         { $result = SafeBooleanConvert $my_config.config.move_to_single_folder }
   }
   
   catch {
      Write-Verbose "... error while retrieving move_to_single_folder element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetSeasonFolderName()
{
   # Define the default result
   # Default to "Season" if nothing else specified
   $result = "Season"
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.season_folder_name -ne "")
         { $result = $my_config.config.season_folder_name }
   }

   catch {
      Write-Verbose "... error while retrieving season_folder_name element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetSeasonNumberFormat()
{
   # Define the default result
   # Default to a two-digit format for season numbers
   $result = "0#"
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.season_number_format -ne "")
         { $result = $my_config.config.season_number_format }
   }
   
   catch {
      Write-Verbose "... error while retrieving season_number_format element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetEpisodeNameFormat()
{
   # Define the default result
   $result = "{0} - S{1}E{2} - {3}"
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.episode_name_format -ne "")
         { $result = $my_config.config.episode_name_format }
   }
   
   catch {
      Write-Verbose "... error while retrieving episode_name_format element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetCreateSeriesFolderIfMissing()
{
   # Define the default result
   # Default to $true - we do create the series folder if it is missing
   $result = $true
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.create_series_folder_if_missing -ne "")
         { $result = SafeBooleanConvert $my_config.config.create_series_folder_if_missing }
   }
   
   catch {
      Write-Verbose "... error while retrieving create_series_folder_if_missing element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetDeleteIfDestExists()
{
   # Define the default result
   # Default to $false - we don't delete if the destination file exists
   $result = $false
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.delete_if_dest_exists -ne "")
         { $result = SafeBooleanConvert $my_config.config.delete_if_dest_exists }
   }
   
   catch {
      Write-Verbose "... error while retrieving delete_if_dest_exists element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetMinAge()
{
   # Define the default result
   # Default to $null - no minimum age
   $result = $null
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.min_age -ne "")
         { $result = $my_config.config.min_age }
   }
   
   catch {
      Write-Verbose "... error while retrieving min_age element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetCharacterChangeMap()
{
   # Define the default result
   # By default, we are not changing any characters
   $result = $null
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.change_char -ne "")
         { $result = $my_config.config.change_char }
   }
   
   catch {
      Write-Verbose "... error while retrieving change_char element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetIgnoreSeries()
{
   # Define the default result
   # By default, we are not ignoring any series
   $result = $null
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.ignore_series -ne "")
         { $result = $my_config.config.ignore_series }
   }
   
   catch {
      Write-Verbose "... error while retrieving ignore_series element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetOnlySeries()
{
   # Define the default result
   # By default, we are not matching only specific series
   $result = $null
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.only_series -ne "")
         { $result = $my_config.config.only_series }
   }
   
   catch {
      Write-Verbose "... error while retrieving only_series element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetCreateUndoLogs()
{
   # Define the default result
   # By default, we WILL create undo logs
   $result = $true
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.create_undo_logs -ne "")
         { $result = SafeBooleanConvert $my_config.config.create_undo_logs }
   }
   
   catch {
      Write-Verbose "... error while retrieving create_undo_logs element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetCreateProcessingLogs()
{
   # Define the default result
   # By default, we WILL create processing logs
   $result = $true
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.create_processing_logs -ne "")
         { $result = SafeBooleanConvert $my_config.config.create_processing_logs }
   }
   
   catch {
      Write-Verbose "... error while retrieving create_processing_logs element: $($_.Exception.Message)"
   }  
   
   Write-Output $result
}

function GetMoveUnmatchedSeries()
{
   # Define the default result
   # By default, we will NOT move unmatched files
   $result = $null

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.move_unmatched_series -ne "")
         { $result = $my_config.config.move_unmatched_series }
   }
   
   catch {
      Write-Verbose "... error while retrieving move_unmatched_series element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetMoveUnmatchedEpisodes()
{
   # Define the default result
   # By default, we will NOT move unmatched files
   $result = $null

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.move_unmatched_episodes -ne "")
         { $result = $my_config.config.move_unmatched_episodes }
   }
   
   catch {
      Write-Verbose "... error while retrieving move_unmatched_episodes element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetMoveDuplicateEpisodes()
{
   # Define the default result
   # By default, we will NOT move duplicate files
   $result = $null

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.move_duplicate_episodes -ne "")
         { $result = $my_config.config.move_duplicate_episodes }
   }
   
   catch {
      Write-Verbose "... error while retrieving move_duplicate_episodes element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetMoveIgnoredSeries()
{
   # Define the default result
   # By default, we will NOT move ignored recordings
   $result = $null

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.move_ignored_series -ne "")
         { $result = $my_config.config.move_ignored_series }
   }
   
   catch {
      Write-Verbose "... error while retrieving move_ignored_series element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetAttributeTitle()
{
   # Define the default result
   $result = "Title"

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.attribute_title -ne "")
         { $result = $my_config.config.attribute_title }
   }
   
   catch {
      Write-Verbose "... error while retrieving attribute_title element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetAttributeDateCreated()
{
   # Define the default result
   $result = "Date Created"

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.attribute_date_created -ne "")
         { $result = $my_config.config.attribute_date_created }
   }
   
   catch {
      Write-Verbose "... error while retrieving attribute_date_created element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetAttributeSubtitle()
{
   # Define the default result
   $result = "Subtitle"

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.attribute_subtitle -ne "")
         { $result = $my_config.config.attribute_subtitle }
   }
   
   catch {
      Write-Verbose "... error while retrieving attribute_subtitle element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetAttributeProgramDescription()
{
   # Define the default result
   $result = "Program Description"

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.attribute_program_description -ne "")
         { $result = $my_config.config.attribute_program_description }
   }
   
   catch {
      Write-Verbose "... error while retrieving attribute_program_description element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetConvertToDVRMS
{
   # Define the default result
   # Default to $false - we don't convert WTV files to DVRMS format
   $result = $false
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.convert_to_dvrms -ne "")
         { $result = SafeBooleanConvert $my_config.config.convert_to_dvrms }
   }
   
   catch {
      Write-Verbose "... error while retrieving convert_to_dvrms element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetDeleteWTVAfterConversion
{
   # Define the default result
   # Default to $false - we don't delete the WTV file after converting it
   $result = $false
   
   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.delete_wtv_after_conversion -ne "")
         { $result = SafeBooleanConvert $my_config.config.delete_wtv_after_conversion }
   }
   
   catch {
      Write-Verbose "... error while retrieving delete_wtv_after_conversion element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

function GetMoveWTVAfterConversion
{
   # Define the default result
   # By default, we will NOT move WTV files after converting them to DVRMS
   $result = $null

   try {
      # Only override the default value if a value has actually been provided!
      if ($my_config.config.move_wtv_after_conversion -ne "")
         { $result = $my_config.config.move_wtv_after_conversion }
   }
   
   catch {
      Write-Verbose "... error while retrieving move_unmatched_episodes element: $($_.Exception.Message)"
   }
   
   Write-Output $result
}

##########################################################################
###
### MAIN CODE STARTS HERE
###
##########################################################################

$my_config = LoadConfigFile
$default_language = GetDefaultLanguage
$data_loc = GetXMLCachePath
$recordings = GetRecordingsPath
$accept_single_bme = GetAcceptSingleBME
$move_to = GetMoveTo
$move_to_single_folder = GetMoveToSingleFolder
$season_folder_name = GetSeasonFolderName
$season_number_format = GetSeasonNumberFormat
$epnameformat = GetEpisodeNameFormat
$create_series_folder_if_missing = GetCreateSeriesFolderIfMissing
$delete_if_dest_exists = GetDeleteIfDestExists
$min_age = GetMinAge
$char_map = GetCharacterChangeMap
$ignore_series = GetIgnoreSeries
$only_series = GetOnlySeries
$create_undo_logs = GetCreateUndoLogs
$create_processing_logs = GetCreateProcessingLogs
$move_unmatched_series = GetMoveUnmatchedSeries
$move_unmatched_episodes = GetMoveUnmatchedEpisodes
$move_duplicate_episodes = GetMoveDuplicateEpisodes
$move_ignored_series = GetMoveIgnoredSeries
$attribute_title = GetAttributeTitle
$attribute_date_created = GetAttributeDateCreated
$attribute_subtitle = GetAttributeSubtitle
$attribute_program_description = GetAttributeProgramDescription
$convert_to_dvrms = GetConvertToDVRMS
$delete_wtv_after_conversion = GetDeleteWTVAfterConversion
$move_wtv_after_conversion = GetMoveWTVAfterConversion

if (($ignore_series -ne $null) -and ($only_series -ne $null))
{
	Throw "Both <ignore_series> and <only_series> have been defined in the XML file. This is not supported."
}

$the_time_is_now = $(Get-Date).ToString("yyyyMMddHHmmss")
if ($create_undo_logs)
{
	# Undo log filename
	$undo_log = "$recordings\UndoRenames_$($the_time_is_now).ps1"
	Write-Host "Undo log is called '$undo_log'"
}
if ($create_processing_logs)
{
	$processing_log = "$recordings\Log_$($the_time_is_now).txt"
	Write-Host "Processing log is called '$processing_log'"
}

Write-HostAndLog "WTV-MetaRenamer v$version"

$shell = New-Object -ComObject "Shell.Application"
$folder = $shell.NameSpace($recordings)

$index_title = -1
$index_date_created = -1
$index_subtitle = -1
$index_program_description = -1

foreach ($index in 0..300)
{
    if ($($folder.GetDetailsOf($null, $index)) -eq $attribute_title)
    {
        Write-VerboseAndLog "... found '$attribute_title' at index $index"
        $index_title = $index
    }
    if ($($folder.GetDetailsOf($null, $index)) -eq $attribute_date_created)
    {
        Write-VerboseAndLog "... found '$attribute_date_created' at index $index"
        $index_date_created = $index
    }
    if ($($folder.GetDetailsOf($null, $index)) -eq $attribute_subtitle)
    {
        Write-VerboseAndLog "... found '$attribute_subtitle' at index $index"
        $index_subtitle = $index
    }
    if ($($folder.GetDetailsOf($null, $index)) -eq $attribute_program_description)
    {
        Write-VerboseAndLog "... found '$attribute_program_description' at index $index"
        $index_program_description = $index
    }
}

if ($index_title -eq -1)
    { Write-HostAndLog "... failed to find attribute '$attribute_title'" }
if ($index_date_created -eq -1)
    { Write-HostAndLog "... failed to find attribute '$attribute_date_created'" }
if ($index_subtitle -eq -1)
    { Write-HostAndLog "... failed to find attribute '$attribute_subtitle'" }
if ($index_program_description -eq -1)
    { Write-HostAndLog "... failed to find attribute '$attribute_program_description'" }

if (($index_title -eq -1) -or ($index_date_created -eq -1) -or ($index_subtitle -eq -1) -or ($index_program_description -eq -1))
    { break }

if (($move_to_single_folder -eq $true) -and ($move_to -is [Array]) -and ($move_to.count -ne 1))
{
	Write-HostAndLog "WARNING! Move-to-single-folder is defined as true but more than one destination folder specified."
}
   
# Get a randomly selected mirror for TvDB XML files
$apikey = "DE8C5EB3A19C799A"
$tvdb_mirror = AllocateDBMirror

CheckForUpdatesSinceLastRun

# If a minimum age has been defined, calculate what date that maps onto.
# Doing this now will simplify later tests.
if ($min_age -ne $null)
{
    $min_age = (Get-Date).AddDays(-([int]$min_age))
	Write-VerboseAndLog "... will only process files older than $min_age"
}

# Now scan through all of the recordings and process
Get-ChildItem -Filter "*.wtv" $recordings | ForEach-Object {
	Write-HostAndLog "Processing $_"
    $file = $folder.ParseName($_.Name)

    $combined_title_and_episode = $false

    $this_title = $($folder.GetDetailsOf($file, $index_title)) # GetFileAttribute $folder $file "Title"
    Write-VerboseAndLog "... title is '$this_title'"
    
    # Before we do ANYTHING else, let's see if the file is old enough.
	$old_enough = $true
    if ($min_age -ne $null)
    {
        $date_created = $($folder.GetDetailsOf($file, $index_date_created)) # GetFileAttribute $folder $file "Date created"
        # This is a string so we need to convert it into a date/time value
        $date_created = [datetime]::ParseExact($date_created, "g", $null)
		Write-VerboseAndLog "... got creation date of $date_created"
        if ($date_created -ge $min_age)
        {
            $old_enough = $false
            Write-HostAndLog "... file isn't old enough; skipping"
        }
    }
    
	if ($old_enough)
	{
	    $series_ID = FetchSeriesID $this_title
	    if ($series_ID -eq $null -and $this_title.IndexOf(":") -ne -1)
	    {
	    	# Let's see if the broadcaster has munged the title and episode name together
	    	$series_ID = FetchSeriesID $($this_title.split(":")[0])
			if ($series_ID -ne $null)
			{
				# Indicate that we may have the episode name in the title string for later parsing
				$combined_title_and_episode = $true
			}
	    }
	    if ($series_ID -eq $null)
	    {
	        Write-HostAndLog "... no series ID retrieved for this recording"
			if ($move_unmatched_series -ne $null)
			{
				# Move the file to the specified location
               	Write-HostAndLog "... moving to '$move_unmatched_series\$_'"
	            Move-Item "$recordings\$_" "$move_unmatched_series\$_" -ErrorAction "SilentlyContinue"
	            if ($?)
	            {
	            	# If we didn't get an error, write the reverse command out to an undo log file
					if ($create_undo_logs)
						{ "Move-Item ""$move_unmatched_series\$_"" ""$recordings\$_""" >> $undo_log }
	            }
	            else
	            {
	            	Write-HostAndLog "... error during move: $($error[0])"
	            }
			}
	    }
		else
		{
			if ((SeriesIsInIgnoreList $series_ID[0]) -eq $true -or (SeriesIsNotInOnlyList $series_ID[0]) -eq $true)
			{
                # We are either ignoring this series, or the series isn't on our "only" list ... which sort of means
                # we are also ignoring it!
                #
                # So, if configured to move ignored episodes, move this one ...
                if ($move_ignored_series)
                {
                    Write-HostAndLog "... moving to $move_ignored_series\$_"
	                Move-Item "$recordings\$_" "$move_ignored_series\$_" -ErrorAction "SilentlyContinue"
	                if ($?)
	                {
	                      # If we didn't get an error, write the reverse command out to an undo log file
		                  if ($create_undo_logs)
				            { "Move-Item ""$move_ignored_series\$_"" ""$recordings\$_""" >> $undo_log }
	                }
	                else
	                {
	                   Write-HostAndLog "... error during move: $($error[0])"
	                }
                }                
                # Then reset the series ID to null so that we don't do anything else with this recording
				$series_ID = $null
			}
		}

		if ($series_ID -ne $null)
	    {
			# Matched the series against the cache/database.
			$this_season = 0
			$this_episode = 0
			# See if we can match the episode name.
			$episodes = FetchEpisodeInfo $series_ID
			if ($episodes -ne $null)
	        {
	            # Start with the simplest approach - the subtitle entry.
	            $subtitle = $($folder.GetDetailsOf($file, $index_subtitle)) # GetFileAttribute $folder $file "Subtitle"
	            if ($subtitle -ne "")
	        	{
	            	Write-VerboseAndLog "... testing against the subtitle metadata"
	            	$result = MatchEpisode $subtitle
	            	$this_season = $result[0]
	            	$this_episode = $result[1]
	           
	            	if ($this_episode -eq 0)
	            	{
	                	# We have a string but it didn't match so let's calculate the edit distances
	                	BestMatchEpisode $subtitle
	              	}
	           	}
	           	if ($this_episode -eq 0)
	           	{
	            	# OK - subtitle entry doesn't work. Another common approach is for the
	            	# description to start with the episode name and be terminated by a colon and a space.
	            	$try_this = $folder.GetDetailsOf($file, $index_program_description) # GetFileAttribute $folder $file "Program description"
	            	$try_this = [regex]::split($try_this, ': ')[0]

	              	Write-VerboseAndLog "... testing against the description and colon delimiter"
	              	$result = MatchEpisode $try_this
	              	$this_season = $result[0]
	              	$this_episode = $result[1]

	              	if ($this_episode -eq 0)
	              	{
	                 	# We have a string but it didn't match so let's calculate the edit distances
	                 	BestMatchEpisode $try_this
	              	}
	           	}
	           	if ($this_episode -eq 0 -and $combined_title_and_episode -eq $true)
	           	{
	              	# We earlier matched against a title string that looked as if it
	              	# was a combination of series name and episode name. Let's see if
	              	# that really is the case.
	              	$colon = $this_title.IndexOf(":")
	              	$try_this = $this_title.substring($colon+1)
	              	$try_this = $try_this.TrimStart()

	              	Write-VerboseAndLog "... testing against title string combo of series and episode"
	              	$result = MatchEpisode $try_this
	              	$this_season = $result[0]
	              	$this_episode = $result[1]

	              	if ($this_episode -eq 0)
	              	{
	                 	# We have a string but it didn't match so let's calculate the edit distances
	                 	BestMatchEpisode $try_this
	              	}
	           	}
	           	if ($this_episode -eq 0)
	           	{
	              	# Look for a title embedded in the description but ending with a full-stop instead of a colon.
	              	$try_this = $folder.GetDetailsOf($file, $index_program_description) # GetFileAttribute $folder $file "Program description"
	            	$try_this = [regex]::split($try_this, '\. ')[0]

	              	Write-VerboseAndLog "... testing against the description and full-stop delimiter"
	              	$result = MatchEpisode $try_this
	              	$this_season = $result[0]
	              	$this_episode = $result[1]

	              	if ($this_episode -eq 0)
	              	{
	                 	# We have a string but it didn't match so let's calculate the edit distances
	                 	BestMatchEpisode $try_this
	              	}
	           	}
	           	if ($this_episode -eq 0)
	           	{
	              	# The BBC sometimes put the title in the description, but prefix it with <episode number>/<episodes in series>.
	              	# Look to see if that pattern has been followed.
	              	$try_this = $folder.GetDetailsOf($file, $index_program_description) # GetFileAttribute $folder $file "Program description"
	              	$split_at = $try_this.IndexOf(". ")
	              	if ($split_at -ne -1)
	              	{
	                  	# Break down the numbers, partly as a sanity check that we have got the correct structure, but
	                  	# also to use the ep number provided to double-check things ... potentially!
	                  	$slash = $try_this.IndexOf("/")
	                  	if ($slash -ne -1 -and $slash -lt $split_at)
	                  	{
	                      	# Strip off the front stuff
	                      	$try_this = $try_this.Substring($split_at+2, $try_this.Length - $split_at - 3)
	                      	# Now look for a colon or full-stop after the episode name and split at
	                      	# whichever comes first.
	                      	$split_at = $try_this.IndexOf(":")
	                      	$fullstop = $try_this.IndexOf(".")
	                      	if ($split_at -eq -1)
	                      	{
	                          	# No colon so use where we found the full-stop
	                          	$split_at = $fullstop
	                      	}
	                      	elseif ($fullstop -ne -1 -and $fullstop -lt $split_at)
	                      	{
	                          	# Full stop comes before a colon - use that
	                          	$split_at = $fullstop
	                      	}
	                      	if ($split_at -ne -1)
	                      	{
	                          	$try_this = $try_this.Substring(0, $split_at)
	                      	}

	                      	Write-VerboseAndLog "... testing against BBC format description field"
	                      	$result = MatchEpisode $try_this
	                      	$this_season = $result[0]
	                      	$this_episode = $result[1]

	                      	if ($this_episode -eq 0)
	                      	{
	                         	# We have a string but it didn't match so let's calculate the edit distances
	                         	BestMatchEpisode $try_this
	                      	}
	                  	}
	              	}
	           	}

	           	# That's all the tests we know to do
	           
	           	if ($this_episode -eq 0)
	           	{
	              	Write-VerboseAndLog "... no precise test"
	              	# If we have 0, we've got one or more results from Best Match.
	              	# If we have ONE match and $accept_single_bme is true, take that one.
	              	# If we have more than one match and $interactive is true, offer the list to the user.

	              	$lowest_score = [int]$($episodes.Data.Episode[0].GetAttribute("ID"))
	              	foreach ($episode in $episodes.Data.Episode)
	              	{
                       # 0.08: changed logic so that scores of -1 are ignored
	                   if (($lowest_score -le 0) -or (([int]$($episode.GetAttribute("ID")) -lt $lowest_score) -and ($episode.EpisodeNumber -ne 0) -and ([int]$($episode.GetAttribute("ID")) -ne -1)))
	                      { $lowest_score = [int]$($episode.GetAttribute("ID")) }
	              	}
	              	Write-VerboseAndLog "... best matches have a score of $lowest_score"

	              	$match_count = 0
	              	foreach ($episode in $episodes.Data.Episode)
	              	{
	                  	if (($($episode.GetAttribute("ID")) -eq $lowest_score) -and ($episode.EpisodeNumber -ne 0))
	                  	{
	                      	$match_count++
	                      	$this_season = [int]$episode.SeasonNumber
	                      	$this_episode = [int]$episode.EpisodeNumber
	                  	}
	              	}

	              	Write-VerboseAndLog "... got $match_count best matches"
	              	if ($match_count -ne 1)
	              	{
	                  	# We've got more than one match - are we running in interactive mode?
	                  	if ($interactive)
	                  	{
	                      	# Yes - display the list and see which one the user picks
	                      	$index = 1
	                      	foreach ($episode in $episodes.Data.Episode)
	                      	{
	                          	if (($($episode.GetAttribute("ID")) -eq $lowest_score) -and ($episode.EpisodeNumber -ne 0))
	                          	{
	                              	$s = $([int]$episode.SeasonNumber).ToString("0#")
	                              	$e = $([int]$episode.EpisodeNumber).ToString("0#")
	                              	Write-Host "... [$index] S$($s)E$($e) - $($episode.EpisodeName)"
	                              	$index++
	                          	}
	                      	}

	                      	# We end up with index being one too high ...
	                      	$index--
	         
	                      	Write-Host "... Enter a number from 1 to $index or RETURN to skip"
	                      	$answer = GetInputFromUser $index
	                      	if ($answer -ne -1)
	                      	{
	                          	# User provided an answer in the correct range so find it
	                          	$index = 1
	                          	foreach ($episode in $episodes.Data.Episode)
	                          	{
	                              	if (($($episode.GetAttribute("ID")) -eq $lowest_score) -and ($episode.EpisodeNumber -ne 0))
	                              	{
	                                  	if ($index -eq $answer)
	                                  	{
	                                      	$this_season = [int]$episode.SeasonNumber
	                                      	$this_episode = [int]$episode.EpisodeNumber
	                                  	}
	                                  	$index++
	                              	}
	                          	}
	                      	}
	                      	else
	                      	{
	                          	# User skipped - set episode to -1 so that we
	                          	# drop through but don't list the "matching" episodes all over again
	                          	$this_episode = -1
	                      	}
	                  	}
	                  	else
	                  	{
	                      	# No - reset $this_episode to 0 so that we drop through to
	                      	# the code below that lists the matches
	                      	$this_episode = 0
	                  	}
	              	}
	           	}

	           	if ($this_episode -gt 0)
	           	{
	              	Write-HostAndLog "... matched against season $this_season and episode $this_episode"
	              	# Retrieve the TvDB version of the episode name
	              	$episode_data = $episodes.Data.Episode | Where-Object { $_.SeasonNumber -eq $this_season -and $_.EpisodeNumber -eq $this_episode }
	              	# Build the name we are going to rename to
                    # v0.12 - define $new_wild to allow us to perform a wildcard Test-Path call to see if the file exists in any format. Note that we do NOT
                    #         put .* at the end of the name as this allows us to check for explicit extensions later on if required
	              	$new_name = "$epnameformat.wtv" -f $($episodes.Data.Series.SeriesName), $($this_season.ToString("0#")), $($this_episode.ToString("0#")), $($episode_data.EpisodeName)
                    $new_wild = "$epnameformat" -f $($episodes.Data.Series.SeriesName), $($this_season.ToString("0#")), $($this_episode.ToString("0#")), $($episode_data.EpisodeName)
	              	# Now perform any required character remapping
	              	Write-VerboseAndLog "... got interim name of $new_name"
	              	$new_name = RemapFilename $new_name
                    $new_wild = RemapFilename $new_wild
	              	Write-VerboseAndLog "... remapped name is $new_name"
	            
	              	# Rename or move?
	              	if ($move_to -ne $null)
	              	{
	                  	# Move - but are we moving to a single folder or to a series structure?
					  	if ($move_to_single_folder -eq $true)
					  	{
	                    	if ($move_to -is [Array])
	                    	{
	                        	$dest_folder = $move_to[0]
	                    	}
	                    	else
	                    	{
	                        	$dest_folder = $move_to
	                    	}
					  	}
					  	else
					  	{
                            # v0.12 - remap the series name
                            $sn = RemapFilename $($episodes.Data.Series.SeriesName)
						  	# let's see if we can find a folder with the series name
		                  	$series_path = $null
	                      	foreach ($path in $move_to)
		                  	{
		                     	Write-VerboseAndLog "... checking $path\$sn"
		                     	if (Test-Path "$path\$sn")
		                     	{
		                        	Write-VerboseAndLog "... found series under path $path"
		                        	$series_path = "$path\$sn"
		                     	}
		                  	}
		                
		                  	# If we didn't find the series AND the setting to create the series folder is false, we have to drop out.
	                      	# Otherwise, we'll create the folder under the first path and move on.
	                      	if (($series_path -ne $null) -or ($create_series_folder_if_missing -eq $true))
	                      	{
	    	                  	if ($series_path -eq $null)
		                      	{
	                             	if ($move_to -is [Array])
	                             	{
		                             	$series_path = "$($move_to[0])\$sn"
	                             	}
	                             	else
	                             	{
		                             	$series_path = "$($move_to)\$sn"
	                             	}
		                         	Write-VerboseAndLog "... creating series folder in $series_path"
		                         	New-Item $series_path -type directory > $null
		                      	}
		                
	    	                  	# Now look for the season folder
		                      	$season_path = $null
		                      	if (Test-Path "$series_path\$season_folder_name $($this_season.ToString("$season_number_format"))")
		                      	{
		                         	$season_path = "$series_path\$season_folder_name $($this_season.ToString("$season_number_format"))"
		                      	}
	    	                  	else
		                      	{
		                         	# If we didn't find the season folder, create it
		                         	$season_path = "$series_path\$season_folder_name $($this_season.ToString("$season_number_format"))"
		                         	Write-VerboseAndLog "... creating season folder in $season_path"
		                         	New-Item $season_path -type directory > $null
		                      	}
						  
	    					  	$dest_folder = $season_path
	                      	}
	                      	else
	                      	{
	                          	# Show that we don't have a destination location
	                          	$dest_folder = ""
	                      	}
					  	}
	                
	                  	if ($dest_folder -eq "")
	                  	{
	                      	Write-HostAndLog "... skipping move as destination location doesn't exist"
	                  	}
	                  	else
	                  	{
	                      	# See if the file already exists there
                            # v0.12 - use $new_wild instead of $new_name
	                      	if (!(Test-Path "$dest_folder\$new_wild.*"))
	                      	{
                                if ($convert_to_dvrms)
                                {
                                    # Call WTVConverter to convert the WTV file to DVRMS
    	                          	Write-HostAndLog "... converting to '$dest_folder\$new_wild.dvr-ms'"
                                    .$env:systemroot\ehome\wtvconverter "$recordings\$_" "$dest_folder\$new_wild.dvr-ms" /ShowUI | out-null
                                    if ($?)
                                    {
                                        # If we didn't get an error, log the fact that we did the conversion and
                                        # finish off the handling
                                        if ($create_undo_logs)
                                            { "# Converted ""$recordings\$_"" to ""$dest_folder\$new_wild.dvr-ms""" >> $undo_log }
                                        if ($delete_wtv_after_conversion)
                                        {
	                              	        Write-HostAndLog "... deleting WTV file after converting to DVR-MS"
	                              	        Remove-Item "$recordings\$_"
                                        }
                                        elseif ($move_wtv_after_conversion)
                                        {
                                            Write-HostAndLog "... converted to DVR-MS, moving to $move_wtv_after_conversion\$_"
	                          	            Move-Item "$recordings\$_" "$move_wtv_after_conversion\$_" -ErrorAction "SilentlyContinue"
	                          	            if ($?)
	                          	            {
	                              	            # If we didn't get an error, write the reverse command out to an undo log file
									            if ($create_undo_logs)
									    	        { "Move-Item ""$move_wtv_after_conversion\$_"" ""$recordings\$_""" >> $undo_log }
	                          	            }
	                          	            else
	                          	            {
	                              	            Write-HostAndLog "... error during move after conversion: $($error[0])"
	                          	            }
                                        }
                                    }
                                    else
                                    {
	                              	    Write-HostAndLog "... error during conversion to DVR-MS: $($error[0])"
                                    }
                                }
                                else
                                {
    	                          	Write-HostAndLog "... moving to '$dest_folder\$new_name'"
	                          	    Move-Item "$recordings\$_" "$dest_folder\$new_name" -ErrorAction "SilentlyContinue"
	                          	    if ($?)
	                          	    {
	                              	    # If we didn't get an error, write the reverse command out to an undo log file
									    if ($create_undo_logs)
										    { "Move-Item ""$dest_folder\$new_name"" ""$recordings\$_""" >> $undo_log }
	                          	    }
	                          	    else
	                          	    {
	                              	    Write-HostAndLog "... error during move: $($error[0])"
	                          	    }
                                }
	                      	}
	                      	else
	                      	{
	                          	if ($delete_if_dest_exists)
	                          	{
	                              	Write-HostAndLog "... file of that name already exists, deleting this one"
	                              	Remove-Item "$recordings\$_"
	                          	}
	                          	elseif ($move_duplicate_episodes)
                                {
                                    Write-HostAndLog "... file of that name already exists, moving to $move_duplicate_episodes\$_"
	                          	    Move-Item "$recordings\$_" "$move_duplicate_episodes\$_" -ErrorAction "SilentlyContinue"
	                          	    if ($?)
	                          	    {
	                              	    # If we didn't get an error, write the reverse command out to an undo log file
									    if ($create_undo_logs)
										    { "Move-Item ""$move_duplicate_episodes\$_"" ""$recordings\$_""" >> $undo_log }
	                          	    }
	                          	    else
	                          	    {
	                              	    Write-HostAndLog "... error during move: $($error[0])"
	                          	    }
                                }
                                else
	                          	{
	                              	Write-HostAndLog "... skipping move as file of that name already exists"
	                          	}
	                      	}
	                  	}
	              	}
	              	else
	              	{
	                 	# Rename - does a file of this name already exist?
                        # v0.12 - use $new_wild instead of $new_name to check for any extension
	                 	if (!(Test-Path "$recordings\$new_wild.*"))
	                 	{
                            if ($convert_to_dvrms)
                            {
                                # Call WTVConverter to convert the WTV file to DVRMS. Pipe to out-null to force PowerShell to wait
    	                      	Write-HostAndLog "... converting to '$new_wild.dvr-ms'"
                                .$env:systemroot\ehome\wtvconverter "$recordings\$_" "$recordings\$new_wild.dvr-ms" /ShowUI | out-null
                                if ($?)
                                {
                                    # If we didn't get an error, log the fact that we did the conversion and
                                    # finish off the handling
                                    if ($create_undo_logs)
                                        { "# Converted ""$recordings\$_"" to ""$recordings\$new_wild.dvr-ms""" >> $undo_log }
                                    if ($delete_wtv_after_conversion)
                                    {
	                          	        Write-HostAndLog "... deleting WTV file after converting to DVR-MS"
	                          	        Remove-Item "$recordings\$_"
                                    }
                                    elseif ($move_wtv_after_conversion)
                                    {
                                        Write-HostAndLog "... converted to DVR-MS, moving to $move_wtv_after_conversion\$_"
	                                    Move-Item "$recordings\$_" "$move_wtv_after_conversion\$_" -ErrorAction "SilentlyContinue"
	                                    if ($?)
	                                    {
	                          	            # If we didn't get an error, write the reverse command out to an undo log file
							                if ($create_undo_logs)
							        	        { "Move-Item ""$move_wtv_after_conversion\$_"" ""$recordings\$_""" >> $undo_log }
	                                    }
	                                    else
	                                    {
	                           	            Write-HostAndLog "... error during move after conversion: $($error[0])"
	                                    }
                                    }
                                }
                                else
                                {
	                                Write-HostAndLog "... error during conversion to DVR-MS: $($error[0])"
                                }
                            }
                            else
                            {
	                     	    Write-HostAndLog "... renaming to '$new_name'"
	                     	    Rename-Item "$recordings\$_" "$new_name" -ErrorAction "SilentlyContinue"
	                     	    if ($?)
	                     	    {
	                         	    # If we didn't get an error, write the reverse command out to an undo log file
								    if ($create_undo_logs)
									    { "Rename-Item ""$recordings\$new_name"" ""$_""" >> $undo_log }
	                     	    }
	                     	    else
	                         	{
	                         	    Write-HostAndLog "... error during rename: $($error[0])"
	                     	    }
                            }
	                 	}
	                 	else
	                 	{
	                     	if ($delete_if_dest_exists)
	                     	{
	                         	Write-HostAndLog "... file of that name already exists, deleting this one"
	                         	Remove-Item "$recordings\$_"
	                     	}
	                        elseif ($move_duplicate_episodes)
                            {
                                Write-HostAndLog "... file of that name already exists, moving to $move_duplicate_episodes\$_"
	                            Move-Item "$recordings\$_" "$move_duplicate_episodes\$_" -ErrorAction "SilentlyContinue"
	                            if ($?)
	                            {
	                                # If we didn't get an error, write the reverse command out to an undo log file
									if ($create_undo_logs)
									    { "Move-Item ""$move_duplicate_episodes\$_"" ""$recordings\$_""" >> $undo_log }
	                          	}
	                          	else
	                          	{
	                                Write-HostAndLog "... error during move: $($error[0])"
	                          	}
                            }
	                     	else
	                     	{
	                         	Write-HostAndLog "... skipping rename as file of that name already exists"
	                     	}
	                 	}
	              	}
	           	}
	           	else
	           	{
	              	Write-HostAndLog "... failed to match TV programme precisely against the database"
	              	# $this_episode can be -1 if we earlier matched against the episode
	              	# database multiple times, or it can be 0 if we didn't match properly at all
	              	# and we've only got Best Matches to work against.
	              	#
	              	# So only list Best Matches, and ignore any entries where the episode number is zero
	              	# as that is a revoked entry in TvDB.
	              	if ($this_episode -eq 0)
	              	{
	                  	$lowest_score = [int]$($episodes.Data.Episode[0].GetAttribute("ID"))
	                  	foreach ($episode in $episodes.Data.Episode)
	                  	{
                            # 0.08: changed logic so that scores of -1 are ignored
	                      	if (($lowest_score -le 0) -or (([int]$($episode.GetAttribute("ID")) -lt $lowest_score) -and ($episode.EpisodeNumber -ne 0) -and ([int]$($episode.GetAttribute("ID")) -ne -1)))
	                          	{ $lowest_score = [int]$($episode.GetAttribute("ID")) }
	                  	}
	                  	Write-VerboseAndLog "... best matches have a score of $lowest_score"
	                  	Write-HostAndLog "... possible matching programmes are:"
	                  	foreach ($episode in $episodes.Data.Episode)
	                  	{
	                      	if (($($episode.GetAttribute("ID")) -eq $lowest_score) -and ($episode.EpisodeNumber -ne 0))
	                      	{
	                          	$s = $([int]$episode.SeasonNumber).ToString("0#")
	                          	$e = $([int]$episode.EpisodeNumber).ToString("0#")
	                          	Write-HostAndLog "... S$($s)E$($e) - $($episode.EpisodeName)"
	                      	}
	                  	}
	              	}
					
					if ($move_unmatched_episodes -ne $null)
					{
						# Move the file to the specified location
		               	Write-HostAndLog "... moving to '$move_unmatched_episodes\$_'"
			            Move-Item "$recordings\$_" "$move_unmatched_episodes\$_" -ErrorAction "SilentlyContinue"
			            if ($?)
			            {
			            	# If we didn't get an error, write the reverse command out to an undo log file
							if ($create_undo_logs)
								{ "Move-Item ""$move_unmatched_episodes\$_"" ""$recordings\$_""" >> $undo_log }
			            }
			            else
			            {
			            	Write-HostAndLog "... error during move: $($error[0])"
			            }
					}
	           	}
	      	}
	    }
	}
}